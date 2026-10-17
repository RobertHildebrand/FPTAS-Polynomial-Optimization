# What Lean verifies

The current audit covers **16 + 12 + 6 = 34 theorems**. Numbering below refers to the current short and extended manuscripts; theorem names are the stable identifiers. Every result is conditional on its displayed Lean hypotheses. An axiom audit does not discharge those hypotheses.

## Scope after the symmetrization revision (October 17, 2026)

The audit now covers the strengthened `D^2 / ell^2` estimate and the actual refinement `max(D^2, ceil(D / sqrt(epsilon)))`, including `ell >= D^2` and the error inequality. The even-part representation is constructed and proved, not assumed. The sharper symmetric-difference factor `4 * floor(D/2)^2` is also verified. Representative bounds, including the multivariate selection theorem, use the new estimate. Finite-instance experiments now use the revised refinement and error budget.

The one-grid mixed-integer proof, finite cover construction and full algorithmic complexity remain outside the formalization. The source and checker hashes in `last_run.json` identify the audited development.

## Paper-to-source map

| Paper argument | Lean declarations | Scope / remaining assumptions |
| --- | --- | --- |
| Lemma 2.2: relative slack widths give feasible extrapolation | [FPTASCalculations](lean/FPTASCalculations.lean): `interval_width`, `slack_extrapolation`, `linear_slack_progression`, `reflecting_cell_progression` | Derives feasibility from linear constraints and interval-width conditions. Does not construct or enumerate the cells. |
| Integer progressions and the positive integer slack gap | [FPTASCalculations](lean/FPTASCalculations.lean): `mixed_integer_progression`, `integer_slack_gap` | Integrality of the specified coordinates/slack is assumed. Not the mixed-integer grid reduction. |
| Lemma 2.6: elementary error algebra | [FPTASCalculations](lean/FPTASCalculations.lean): `sampled_sup_algebra`, `second_difference_transfer` | Scalar absorption and transfer from a second-difference estimate. |
| Lemma 2.6: sampled Markov estimate | [SampledMarkov](lean/SampledMarkov.lean): `markov_difference`, `nearest_integer`, `sampled_sup_bound`, `second_difference_bound`, `sampled_markov` | Proves the D^2/ell^2 estimate from the two explicit classical Markov hypotheses, rounding and maximum attainment. `second_difference_bound` is a retained helper from the earlier proof, not used by the strengthened lemma. |
| Lemma 2.6: symmetrization | [SampledMarkov](lean/SampledMarkov.lean): `coeff_reflect`, `degree_contract`, `even_contract`, `symmetrized_difference` | Constructs h from even coefficients, proves its degree bound and h(t²) = (q(t)+q(-t))/2, then derives the sharper half-degree estimate. |
| Proposition 2.7: restriction to a line | [LineRestriction](lean/LineRestriction.lean): `eval_restrict`, `eval_zero`, `eval_one`, `degree_restrict` | Constructs the restriction of an actual multivariate polynomial and proves its degree bound. |
| Proposition 2.7: approximation at extrema and selection | [SampledMarkov](lean/SampledMarkov.lean): `representative_at_minimum`, `representative_at_maximum`, `select_representative`; [LineRestriction](lean/LineRestriction.lean): `multivariate_representative`, `multivariate_selection` | Assumes feasible progression samples, global bounds, degree and Markov hypotheses. The multivariate theorems discharge the univariate restriction interface. They do not assemble the finite cover. |
| Theorem 1.1: refinement parameter and abstract selection | [FPTASCalculations](lean/FPTASCalculations.lean): `refinement_error`, `ceiling_refinement`, `representative_range_guarantee` | Checks D²/ell² ≤ epsilon, positivity and ell ≥ D² for the maximum/ceiling choice, and selection given a good representative. Not the complete algorithm or runtime. |
| Corollary 1.2: nonnegative maximization | [FPTASCalculations](lean/FPTASCalculations.lean): `nonnegative_maximization` | Converts a range-relative error to the multiplicative bound assuming a nonnegative minimum. |
| Discussion / extended Appendix A: local surrogate principle | [FPTASCalculations](lean/FPTASCalculations.lean): `local_comparison`, `uniform_model_error`, `cover_solve_select`, `empty_candidates_iff` | Proves conditional error and infeasibility transfers; assumes coverage and sound, complete local oracles. Does not implement them. |

## The boundary of the formalization

`MarkovBound` in [SampledMarkov.lean](lean/SampledMarkov.lean) is a conjunction of two propositions passed as hypotheses, not a new Lean axiom. `CenteredMarkovBound D T` is the classical derivative estimate on [-T,T] with factor D²/T. `IntervalMarkovBound (D/2) 0 (T²)` is the classical estimate on [0,T²] with factor 2 floor(D/2)²/T². Both are applications of the same established inequality, with different degrees and intervals. No even-part identity, degree bound or symmetrization error estimate is included in the assumptions.

The proof chain is: relative slack widths imply feasible progressions; affine substitution gives a univariate polynomial; sampled Markov control gives an error near an optimum; finite selection preserves that guarantee. These components have been checked, but their assembly with the algorithm's actual cover has not been formalized.

**Not verified in Lean:** Lemma 2.1's coordinate/encoding estimates; finite cover construction and coverage; Lemma 2.4's face count, incremental enumeration and bit complexity; the full equivalence in Remark 2.3; the parallel-family count; local oracle implementations; Corollary 1.3's mixed-integer grid reduction; or the full running-time theorem. `ReflectingCells.lean` and `check_reflecting.py` are historical explorations and are not included in the checked suite.

## Running and interpreting the audit

Follow the root README's setup, then run `python3 verification/check_all.py` from the repository root. This uses Python's standard library only. Individual checks remain available:

```sh
python3 verification/lean/check_fptas_calculations.py
python3 verification/lean/check_sampled_markov.py
python3 verification/lean/check_line_restriction.py
```

To reuse an already compiled dependency tree with exactly the locked revisions:

```sh
python3 verification/check_all.py --packages-dir /absolute/path/to/.lake/packages
```

The scripts verify dependency Git revisions, compile the source, and use `#print axioms` for every theorem. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. A compiler failure, missing axiom report, `sorryAx` or other axiom makes the check fail. A normal `lake build` compiles the modules but does not replace this axiom audit.

Each module has a `*_verification_log.txt`. The aggregate command writes `last_run.json` with UTC time, source/checker hashes, pinned toolchain, exit codes and overall success. This file is refreshed at the start, so an interrupted or failed run cannot leave a previous aggregate success as the current result. Logs are evidence for the recorded sources, not a substitute for rerunning the checker after edits.

If `elan` is missing, install elan and put its binaries on PATH. If packages or compiled imports are missing, run `lake exe cache get` inside `verification/lean`. If a revision differs, use a fresh checkout with the committed manifest, rather than changing the manifest to silence the check. The checker does not install dependencies or access the network itself.

With `--experiments`, the finite-instance script also runs and refreshes `experiments/results.json`. These tests enumerate small bounded domains using exact arithmetic; they do not prove the general theorem or its complexity.
