# Working on the manuscript and verification

## Entry points

The short manuscript is `reflecting_cells_fptas_short.tex`; the extended manuscript is `reflecting_cells_fptas.tex`. The review draft is generated from the short source by `verification/make_review_draft.py`. Edit the annotation generator for durable changes to review notes, then regenerate the review draft.

Keep statements of formal coverage conditional on the hypotheses in the Lean declarations. Do not equate a successful axiom audit with verification of the entire algorithm or its implementation.

## Before sharing mathematical changes

1. Update the relevant Lean source, its coverage notes in `verification/README.md`, and the review annotations.
2. Regenerate the review draft with `python3 verification/make_review_draft.py`.
3. Compile the edited LaTeX documents and inspect their layout.
4. Run `python3 verification/check_all.py` after the drafts and documentation are final. The record captures their hashes at the start of the run.
5. Run `python3 verification/check_all.py --check-record` to check that the record still matches.
6. Include changed sources, checkers, documentation, audit logs and `verification/last_run.json` together.

A documentation-only README edit also changes a recorded hash. Rerun the aggregate audit rather than manually editing its success flag or hashes. Never commit `.lake` build caches or machine-specific dependency paths. Reuse a pinned local dependency tree with the checker's `--packages-dir` option when appropriate.

The current aggregate audit includes eight modules; historical `ReflectingCells.lean` is intentionally excluded. A new module must be added to the build roots, aggregate checker, source-hash list, and coverage documentation.

## Interactive guide changes

Run `node --test docs/explorer.test.js`, then test the page in a browser. Keep the guide offline-capable and dependency-free. Distinguish observed small-instance behavior from proved guarantees. The page's explicit theorem count must match the current audited modules.

Keep source and generated assets clearly separated. Avoid moving the manuscript or checked Lean files solely for tidiness: the review generator, audit record, and external links use their stable paths.
