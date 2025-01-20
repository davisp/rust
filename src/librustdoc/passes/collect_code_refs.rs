//! Find and resolve all codeblock references
//!
//! This pass searches for all of the `rust,{source="somemode::some_fn"}`
//! code references and resolves them to actual source code that will be used
//! while rendering the code blocks.
use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use super::Pass;
use crate::clean::*;
use crate::core::DocContext;
use crate::html::markdown::{self, ErrorCodes, Ignore, LangString, MdRelLine};
use crate::visit::DocVisitor;

pub(crate) const COLLECT_CODE_REFS: Pass = Pass {
    name: "collect_code_refs",
    run: Some(collect_code_refs),
    description: "collect source code for doc code source references",
};

pub(crate) fn collect_code_refs(krate: Crate, cx: &mut DocContext<'_>) -> Crate {
    let mut coll = CodeRefCollector { cx, mod_path: vec![], refs: Default::default() };
    coll.visit_crate(&krate);

    let mut refs = coll.refs;
    let mut res =
        CodeRefResolver { cx, mod_path: vec![], refs: refs.clone(), resolved: Default::default() };
    res.visit_crate(&krate);

    let resolved = res.resolved;

    #[allow(rustc::potential_query_instability)]
    for source_ref in refs.drain().collect::<Vec<_>>() {
        if resolved.get(&source_ref).is_none() {
            // TODO: Make these actual error messages.
            panic!("Missing source reference: {}", source_ref);
        }
    }

    // Set the resolved source refs on the cache so we can emit the source
    // code when rendering code blocks.
    cx.cache.source_refs = resolved;

    krate
}

struct CodeRefCollector<'a, 'tcx> {
    cx: &'a mut DocContext<'tcx>,
    mod_path: Vec<String>,
    refs: FxHashSet<String>,
}

impl<'a, 'tcx> CodeRefCollector<'a, 'tcx> {
    pub fn gather_tests(&mut self, dox: &str, item: &Item) {
        let Some(_) = DocContext::as_local_hir_id(self.cx.tcx, item.item_id) else {
            // If non-local, no need to check anything.
            return;
        };

        markdown::find_testable_code(dox, self, ErrorCodes::No, false, None);
    }

    fn add_ref(&mut self, source: &str) {
        let source_ref = calculate_ref(&self.mod_path[..], source);
        self.refs.insert(source_ref);
    }
}

impl DocVisitor<'_> for CodeRefCollector<'_, '_> {
    fn visit_item(&mut self, item: &Item) {
        if matches!(item.inner.kind, ItemKind::ModuleItem(_)) {
            self.mod_path
                .push(item.name.map(|s| s.as_str().to_owned()).unwrap_or("<unknown>".to_string()));
        }

        self.gather_tests(&item.doc_value(), item);
        self.visit_item_recur(item);

        if matches!(item.inner.kind, ItemKind::ModuleItem(_)) {
            self.mod_path.pop();
        }
    }
}

impl crate::doctest::DocTestVisitor for CodeRefCollector<'_, '_> {
    fn visit_test(&mut self, _: String, config: LangString, _: MdRelLine) {
        let Some(source) = config.source else {
            return;
        };

        if config.rust && config.ignore == Ignore::None {
            self.add_ref(&source)
        }
    }
}

struct CodeRefResolver<'a, 'tcx> {
    cx: &'a mut DocContext<'tcx>,
    mod_path: Vec<String>,
    refs: FxHashSet<String>,
    resolved: FxHashMap<String, String>,
}

impl<'a, 'tcx> CodeRefResolver<'a, 'tcx> {}

impl DocVisitor<'_> for CodeRefResolver<'_, '_> {
    fn visit_item(&mut self, item: &Item) {
        if matches!(item.inner.kind, ItemKind::ModuleItem(_)) {
            self.mod_path
                .push(item.name.map(|s| s.as_str().to_owned()).unwrap_or("<unknown>".to_string()));
        }

        if matches!(item.inner.kind, ItemKind::FunctionItem(_)) {
            self.mod_path
                .push(item.name.map(|s| s.as_str().to_owned()).unwrap_or("<unknown>".to_string()));
            let source_ref = self.mod_path.join("::");
            self.mod_path.pop();

            if self.refs.contains(&source_ref) {
                // Safety: Lol, hacking
                let def_id = item.def_id().unwrap().as_local().unwrap();
                let tcx = self.cx.tcx;
                let body = tcx.hir().body_owned_by(def_id);
                let span = body.value.span;
                let source =
                    tcx.sess.source_map().span_to_snippet(span).expect("Error getting source code");
                let source = dedent(source.trim().trim_start_matches('{').trim_end_matches('}'));
                self.resolved.insert(source_ref, source.to_string());
            }
        }

        self.visit_item_recur(item);

        if matches!(item.inner.kind, ItemKind::ModuleItem(_)) {
            self.mod_path.pop();
        }
    }
}

pub(crate) fn calculate_ref(mod_path: &[String], source: &str) -> String {
    let parts = source.split("::").collect::<Vec<_>>();
    assert!(parts.len() >= 1);
    let (mut path, offset) = if parts[0].to_ascii_lowercase() == "crate" && mod_path.len() > 1 {
        (vec![mod_path[0].to_owned()], 1)
    } else if parts[0].to_ascii_lowercase() == "super" && mod_path.len() > 1 {
        (mod_path[0..mod_path.len() - 1].iter().map(|s| s.to_owned()).collect::<Vec<_>>(), 1)
    } else {
        (mod_path.iter().map(|s| s.to_owned()).collect::<Vec<_>>(), 0)
    };

    let parts = parts.into_iter().skip(offset).map(|s| s.to_owned()).collect::<Vec<_>>();
    path.extend(parts);

    path.join("::")
}

pub fn dedent(s: &str) -> String {
    use std::ops::ControlFlow;

    // First find the longest common whitespace prefix in characters.
    let prefix = s.lines().fold(None, |prefix, line| {
        let len = line.char_indices().try_for_each(|(idx, char)| {
            if char.is_whitespace() { ControlFlow::Continue(()) } else { ControlFlow::Break(idx) }
        });

        // If we didn't find a non-whitespace character, just skip this line
        // by returning the current prefix.
        let curr_prefix = match len {
            ControlFlow::Continue(()) => return prefix,
            ControlFlow::Break(idx) => &line[..idx],
        };

        // Extract the existing prefix or return curr_prefix if its the first
        // one found.
        let prefix = if let Some(prefix) = prefix {
            prefix
        } else {
            return Some(curr_prefix);
        };

        let iter =
            prefix.char_indices().zip(curr_prefix.chars()).try_for_each(|((idx, c1), c2)| {
                if c1 == c2 { ControlFlow::Continue(()) } else { ControlFlow::Break(idx) }
            });

        match iter {
            ControlFlow::Continue(()) => Some(prefix),
            ControlFlow::Break(idx) => Some(&prefix[..idx]),
        }
    });

    // Extract the prefix or return an empty string if no prefix was found.
    let prefix = if let Some(prefix) = prefix {
        prefix.len()
    } else {
        return String::new();
    };

    // Remove the prefix from all linees that have non-whitespace characters.
    let (dedented, _) =
        s.lines().fold((String::with_capacity(s.len()), 0), |(mut curr, blanks), line| {
            if line.chars().all(|c| c.is_whitespace()) {
                return (curr, blanks + 1);
            }

            // We found a non-empty line, if we have data in `curr` then we need
            // to add `blank` empty lines.
            if !curr.is_empty() {
                (0..blanks).for_each(|_| curr.push('\n'))
            }

            curr.extend(line[prefix..].chars());
            (curr, 1)
        });

    dedented
}
