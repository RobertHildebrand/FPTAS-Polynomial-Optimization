# Polynomial approximation by reflecting cells

The standalone manuscript is `reflecting_cells_fptas.tex`. All figures are embedded TikZ/PGFPlots, including a pentagonal slack-cell example. Compile with a LaTeX installation supporting the packages in its preamble, or the Codex document editor.

## Formal verification

`verification/lean/` contains 30 checked results in three modules:

- `FPTASCalculations.lean`: 16 algebraic, geometric, and abstract selection results.
- `SampledMarkov.lean`: 8 analytic and representative-transfer results, conditional on the classical scaled Markov inequality as an explicit hypothesis.
- `LineRestriction.lean`: 6 affine substitution, degree, and multivariate approximation results.

The checked results contain no `sorry` or custom axioms. The logs record only `propext`, `Classical.choice`, and `Quot.sound`. Cover construction, assembly of the full algorithm, and runtime bounds are not formally verified. `ReflectingCells.lean` is an earlier unchecked exploration, excluded from the default build.

From `verification/lean`, install the pinned dependencies with `lake update` and `lake exe cache get`, then run:

```sh
python3 check_fptas_calculations.py
python3 check_sampled_markov.py
python3 check_line_restriction.py
```

Each checker also accepts `--packages-dir /absolute/path/to/existing/.lake/packages` to reuse compiled dependencies. It checks their Git revisions against the manifest. The line-restriction checker rebuilds its sampled-Markov dependency.

## Experiments

`experiments/check_reflecting_cells.py` and `experiments/results.json` provide exhaustive small-instance checks. This is a correctness experiment, not an implementation achieving the stated complexity.

## Provenance

Copied on October 14, 2026 from the `polynomial_fptas` directory and FPTAS verification modules in the local `Unbounded-Cubic-Integer-Programming` repository. The source manuscript remains there because it was open in the editor during transfer. The disclosure's reference to 45 earlier cubic calculations concerns that original repository; those unrelated files are not included here.
