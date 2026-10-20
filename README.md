# Polynomial approximation by reflecting cells

Start with the [short, two-column paper](reflecting_cells_fptas_short.tex). The [extended paper](reflecting_cells_fptas.tex) includes additional discussion and a detailed account of AI assistance and formal verification. Both are standalone LaTeX sources with embedded figures.

## Reproduce the verification

**256 Lean theorems are checked; the entire FPTAS is not formally verified.** The development now proves the symmetrization identity, its degree bound, the strengthened `D^2 / ell^2` approximation estimate, and the refinement `max(D^2, ceil(D / sqrt(epsilon)))`. Classical Markov inequalities remain explicit hypotheses. The half-unit right-hand-side shift, equality of integer feasible sets, and the closed shifted-slack-to-progression connection are checked, as is the conditional mixed-integer error transfer. The revised grid checks include actual upward-rounded barycentric weights, residual convex weights, the coordinatewise segment and grid identities, and the Markov-based grid multiplier. Integral-slice scaling and Caratheodory representations remain external inputs; `mixed_integer_reduction` now assembles convex rounding, grid membership, actual polynomial scaling and the error transfer. The denominator-cleared polynomial is now constructed over the integers, with its evaluation identity, unchanged support and degree proved. The scaled feasible-set bijection and polynomial coefficient binary-length bounds and scaled constraint encoding bounds are now checked. Rational constraint denominator clearing now has verified feasibility and encoding bounds. Determinant, coordinate-exponent, convex-combination and slack estimates are also checked, conditional on Cramer data and a convex representation of each point. The actual determinant/lcm size estimates and the mixed-integer exponent calculation are checked under explicit encoding and subroutine cost hypotheses. The actual rational grid-multiplier bit bound, combined scaled-input payload (including epsilon/2), and shifted integer-slack interval rounding are also checked. The short-version CHKM exponent translation is checked under explicit published hypotheses. Threshold coverage and the geometric chamber-count theorem are now proved: ChamberInsertion establishes the split-chamber injection, dimension reduction, and binomial bound for the actual retained chamber family. The new `chamber_approximation` proves coverage and relative widths for closures of the actual slack-threshold sign regions, including boundary points, and connects them to the approximation guarantee. The retained closures are now proved equal to explicit rational halfspace systems, compressed to two slack bounds per original row; rounded integer membership tests are also checked. The common-margin LP criterion for nonempty interior is proved for both full and compressed systems, assuming proper rows and a feasible optimal LP solution. Threshold and compressed-cell coefficient payloads are checked in `CellEncoding`, including reduced rational thresholds, original right-hand sides, rounded integer rows, and common-margin LP overhead. Complete LP query encoding now includes the objective and an explicit metadata schema; a concrete polynomial query-size bound is checked using the actual refinement and explicit input-parameter bounds. Enumeration, oracle implementations, arithmetic costs and full bit complexity remain mathematical proofs in the paper.

See the **[paper-to-Lean coverage guide](verification/README.md)** for exact declarations, assumptions, exclusions and troubleshooting.

With Python 3, Git and [elan](https://github.com/leanprover/elan) installed, run from this repository:

```sh
cd verification/lean
lake exe cache get
cd ../..
python3 verification/check_all.py
```

The committed toolchain and dependency manifest pin Lean and Mathlib. Do not run `lake update` as part of reproduction: it can change the dependency lock. The first setup needs network access and disk space for Lean/Mathlib. The checker rebuilds all eight modules and audits every theorem's transitive axioms. Expected total: **256 theorems; no custom axioms or sorryAx**.

Optionally include the exact small-instance experiments:

```sh
python3 verification/check_all.py --experiments
```

These experiments are independent sanity checks, not an implementation with the paper's running-time bound. The original unshifted tests include a negative control showing why refinement matters. The current `check_shifted_chambers.py` enumerates exact rational polygons, checks boundary overlaps and a lower-dimensional original polytope, and verifies integer feasibility, progression samples and approximation against exhaustive optima. Run it directly with `python3 experiments/check_shifted_chambers.py`.

## Build the papers

With a standard LaTeX installation including TikZ and PGFPlots:

```sh
pdflatex -interaction=nonstopmode -halt-on-error reflecting_cells_fptas_short.tex
pdflatex -interaction=nonstopmode -halt-on-error reflecting_cells_fptas_short.tex
```

Use `reflecting_cells_fptas.tex` instead for the extended version. Two passes resolve cross-references; no external bibliography database or image files are required.

## Files and provenance

- `verification/lean/`: checked sources, pinned dependencies and individual audit logs.
- `verification/check_all.py`: single entry point; records source hashes and run status.
- `experiments/`: exhaustive finite-instance tests and their results.

The project was transferred from `Unbounded-Cubic-Integer-Programming` on October 14, 2026. The 45 earlier cubic calculations mentioned in the extended disclosure belong to that separate project and do not certify this FPTAS. `verification/lean/ReflectingCells.lean` is an unchecked historical exploration, excluded from the build and audit.

## Review the accompanying draft

`python3 verification/make_review_draft.py` regenerates `reflecting_cells_fptas_review.tex` from the short submission source. Blue notes mark conditional Lean coverage; amber notes identify human-review obligations. The review copy is not a submission layout or a certification of the whole paper. See `verification/reference_audit.txt` for the reference audit and its remaining limitations.

`python3 verification/check_all.py --check-record` checks whether the successful audit record still matches the current drafts and checked sources; it does not rerun Lean. Run the full check after any mathematical changes.
