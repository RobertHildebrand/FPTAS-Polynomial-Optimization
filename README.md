# Polynomial approximation by reflecting cells

Start with the [short, two-column paper](reflecting_cells_fptas_short.tex). The [extended paper](reflecting_cells_fptas.tex) includes additional discussion and a detailed account of AI assistance and formal verification. Both are standalone LaTeX sources with embedded figures.

## Reproduce the verification

**34 Lean theorems are checked; the entire FPTAS is not formally verified.** The development now proves the symmetrization identity, its degree bound, the strengthened `D^2 / ell^2` approximation estimate, and the refinement `max(D^2, ceil(D / sqrt(epsilon)))`. Classical Markov inequalities remain explicit hypotheses. Cover construction, enumeration, the mixed-integer reduction and bit complexity remain mathematical proofs in the paper.

See the **[paper-to-Lean coverage guide](verification/README.md)** for exact declarations, assumptions, exclusions and troubleshooting.

With Python 3, Git and [elan](https://github.com/leanprover/elan) installed, run from this repository:

```sh
cd verification/lean
lake exe cache get
cd ../..
python3 verification/check_all.py
```

The committed toolchain and dependency manifest pin Lean and Mathlib. Do not run `lake update` as part of reproduction: it can change the dependency lock. The first setup needs network access and disk space for Lean/Mathlib. The checker rebuilds all three modules and audits every theorem's transitive axioms. Expected total: **34 theorems; no custom axioms or sorryAx**.

Optionally include the exact small-instance experiments:

```sh
python3 verification/check_all.py --experiments
```

These experiments are independent sanity checks, not an implementation with the paper's running-time bound. They include a negative control showing why refinement matters.

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
