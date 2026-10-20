# What Lean verifies

The current audit covers **31 + 13 + 15 + 49 = 108 theorems**. Where numbering differs, both short and extended numbers are given; theorem names are the stable identifiers. Every result is conditional on its displayed Lean hypotheses. An axiom audit does not discharge those hypotheses.

## Scope after the symmetrization revision (October 17, 2026)

The audit now covers the strengthened `D^2 / ell^2` estimate and the actual refinement `max(D^2, ceil(D / sqrt(epsilon)))`, including `ell >= D^2` and the error inequality. The even-part representation is constructed and proved, not assumed. The sharper symmetric-difference factor `4 * floor(D/2)^2` is also verified. Representative bounds, including the multivariate selection theorem, use the new estimate. Finite-instance experiments now use the revised refinement and error budget.

The conditional one-grid error transfer, compatible-grid parameter arithmetic, positive objective scaling and grid nonemptiness are now checked. Constructing the compatible grid, deriving the range lower bound, finite cover construction and full algorithmic complexity remain outside the formalization. The manuscript, source and checker hashes in `last_run.json` identify the audited development.

## Shifted closed chambers (October 19, 2026)

Both manuscripts now use shifted right-hand sides b+1/2 and closed full-dimensional chambers inside Q. LineRestriction adds six verified theorems: `integer_row_value` constructs an integer row value from actual integer coefficients; `integer_half_shift` proves the scalar integer gap; `shifted_feasible_iff` identifies the two integer feasible sets; `shifted_slack_positive` proves the half-unit margin; `shifted_slack_integral_progression` returns the integer samples from the relaxation to the original set; and `shifted_slack_cover_guarantee` assembles the final error guarantee from closed interval-width hypotheses.

The shift applies after the mixed-integer grid reduction, not directly to mixed-integer constraints. Coverage by chamber closures, the nonempty-interior LP, the chamber count and the rounding/encoding discussion remain human-review obligations. The older unshifted slack theorems remain checked auxiliary results; their zero-slack branches are no longer needed by the manuscript's construction. Determinant proofs still concern the original coordinate bounds; the added half-unit in the upper slack estimate is accounted for in the manuscript, not by a new determinant theorem.

## Paper-to-source map

| Paper argument | Lean declarations | Scope / remaining assumptions |
| --- | --- | --- |
| Lemma 2.1 (short) / 2.2 (extended): relative slack widths give feasible extrapolation | [FPTASCalculations](lean/FPTASCalculations.lean): `interval_width`, `slack_extrapolation`, `linear_slack_progression`, `reflecting_cell_progression` | Derives feasibility from linear constraints and interval-width conditions. Does not construct or enumerate the cells. |
| Integer progressions and the positive integer slack gap | [FPTASCalculations](lean/FPTASCalculations.lean): `mixed_integer_progression`, `integer_slack_gap` | Integrality of the specified coordinates/slack is assumed. Not the mixed-integer grid reduction. |
| Lemma 2.5 (short) / 2.6 (extended): elementary error algebra | [FPTASCalculations](lean/FPTASCalculations.lean): `sampled_sup_algebra`, `second_difference_transfer` | Scalar absorption and transfer from a second-difference estimate. |
| Lemma 2.5 (short) / 2.6 (extended): sampled Markov estimate | [SampledMarkov](lean/SampledMarkov.lean): `markov_difference`, `nearest_integer`, `sampled_sup_bound`, `second_difference_bound`, `sampled_markov` | Proves the D^2/ell^2 estimate from the two explicit classical Markov hypotheses, rounding and maximum attainment. `second_difference_bound` is a retained helper from the earlier proof, not used by the strengthened lemma. |
| Lemma 2.5 (short) / 2.6 (extended): symmetrization | [SampledMarkov](lean/SampledMarkov.lean): `coeff_reflect`, `degree_contract`, `even_contract`, `symmetrized_difference` | Constructs h from even coefficients, proves its degree bound and h(t²) = (q(t)+q(-t))/2, then derives the sharper half-degree estimate. |
| Proposition 2.6 (short) / 2.7 (extended): restriction to a line | [LineRestriction](lean/LineRestriction.lean): `eval_restrict`, `eval_zero`, `eval_one`, `degree_restrict` | Constructs the restriction of an actual multivariate polynomial and proves its degree bound. |
| Proposition 2.6 (short) / 2.7 (extended): approximation at extrema and selection | [SampledMarkov](lean/SampledMarkov.lean): `representative_at_minimum`, `representative_at_maximum`, `select_representative`; [LineRestriction](lean/LineRestriction.lean): `multivariate_representative`, `multivariate_selection` | Assumes feasible progression samples, global bounds, degree and Markov hypotheses. The multivariate theorems discharge the univariate restriction interface. They do not construct the finite cover. |
| Theorem 1.1: refinement parameter and abstract selection | [FPTASCalculations](lean/FPTASCalculations.lean): `refinement_error`, `ceiling_refinement`, `representative_range_guarantee` | Checks D²/ell² ≤ epsilon, positivity and ell ≥ D² for the maximum/ceiling choice, and selection given a good representative. Not the complete algorithm or runtime. |
| Corollary 1.2: nonnegative maximization | [FPTASCalculations](lean/FPTASCalculations.lean): `nonnegative_maximization` | Converts a range-relative error to the multiplicative bound assuming a nonnegative minimum. |
| Discussion / extended Appendix A: local surrogate principle | [FPTASCalculations](lean/FPTASCalculations.lean): `local_comparison`, `uniform_model_error`, `cover_solve_select`, `empty_candidates_iff` | Proves conditional error and infeasibility transfers; assumes coverage and sound, complete local oracles. Does not implement them. |
| Theorem 1.1: conditional cover-to-error assembly | [LineRestriction](lean/LineRestriction.lean): `certified_cover_guarantee` | Combines coverage, complete feasible representatives and reflecting progressions with the actual maximum/ceiling refinement. Assumes these cover properties and Markov; proves the epsilon error, feasible selection and nonnegativity. No algorithm or bit complexity. |

| Auxiliary unshifted slack and integrality connection | [LineRestriction](lean/LineRestriction.lean): `slack_integral_progression`, `slack_cover_guarantee` | Defines the feasible set by linear inequalities and integral coordinates, derives all progression samples from rowwise widths, then obtains the epsilon guarantee. Assumes cell coverage, feasible/complete candidates, extrema and Markov. |
| Corollary 1.3: Markov-based grid reduction | FPTASCalculations: `rounded_barycentric_weights`, `rounded_segment_weights`, `barycentric_coordinate_segment`, `rounded_grid_coordinate`, `markov_grid_multiplier`, `markov_grid_multiplier_bounds`, `markov_grid_transfer`; SampledMarkov: `unit_interval_markov_error` | Verifies ceiling rounding, residual convex weights, coordinatewise segment/grid identities, multiplier bounds and error composition. Classical Markov, integral-slice scaling, Caratheodory representations, geometric assembly and full complexity remain external or human-checked. |

| Corollary 1.3: scaled polynomial | [ScaledPolynomial](lean/ScaledPolynomial.lean): `weight_le`, `coefficient`, `support_scaled`, `degree_bound`, `degree_preserved`, `monomial_substitution`, `eval_scaled`, `integer_representation` | Constructs an actual integer-coefficient MvPolynomial. Proves evaluation equals Q^D f(u/Q,z), identical support and degree for nonzero integer Q, and degree at most D. Assumes only nonzero Q and the input degree bound; no substitution identity or integrality is assumed. Feasible-set identification and polynomial coefficient bit lengths are proved below. Scaled matrix/right-hand-side bit lengths are proved below; their construction cost and full runtime remain external. |

| Corollary 1.3: scaled feasible set | [ScaledPolynomial](lean/ScaledPolynomial.lean): `decode_encode`, `encode_decode`, `row_identity`, `grid_coordinates`, `scaled_feasible_iff`, `grid_feasible_iff`, `feasible_bijection` | Defines integer scaled rows: keep continuous columns, multiply the other columns and right-hand side by positive Q. Proves an actual bijection with the compatible-grid feasible set. Grid existence/construction is not assumed by these identities and is not proved here. |
| Corollary 1.3: coefficient binary lengths | [ScaledPolynomial](lean/ScaledPolynomial.lean): `bitSize_eq_clog`, `size_mul_le`, `size_mul_pow_le`, `coefficient_bits`, `coefficient_payload` | Proves signed bit length is 1 + Nat.clog 2 (abs(c)+1), the per-coefficient bound by bitSize(c)+D*size(abs(Q)), and summed coefficient-payload growth. No asymptotic runtime or cost of constructing Q is asserted. |

| Current shifted construction and Theorem 1.1 | [LineRestriction](lean/LineRestriction.lean): `integer_row_value`, `integer_half_shift`, `shifted_feasible_iff`, `shifted_slack_positive`, `shifted_slack_integral_progression`, `shifted_slack_cover_guarantee` | Checks integer row evaluation, the half-unit relaxation, positive slack, and the final guarantee from closed shifted intervals. Coverage, oracle completeness, extrema and Markov remain hypotheses; chamber counting and enumeration are not formalized. |

## The boundary of the formalization

`MarkovBound` in [SampledMarkov.lean](lean/SampledMarkov.lean) is a conjunction of two propositions passed as hypotheses, not a new Lean axiom. `CenteredMarkovBound D T` is the classical derivative estimate on [-T,T] with factor D²/T. `IntervalMarkovBound (D/2) 0 (T²)` is the classical estimate on [0,T²] with factor 2 floor(D/2)²/T². Both are applications of the same established inequality, with different degrees and intervals. No even-part identity, degree bound or symmetrization error estimate is included in the assumptions.

The proof chain is: relative slack widths imply feasible progressions; affine substitution gives a univariate polynomial; sampled Markov control gives an error near an optimum; finite selection preserves that guarantee. The new `LineRestriction.certified_cover_guarantee` assembles the analytic error estimate and actual refinement with an abstract finite cover. Coverage, sound/complete representatives, feasible progressions, an attained minimizer, global bounds, and the classical Markov inequalities are explicit hypotheses. The auxiliary `slack_cover_guarantee` wires the rowwise slack hypotheses and coordinate integrality into this theorem through `slack_integral_progression`. Progression feasibility is a conclusion, not an input. The current `shifted_slack_cover_guarantee` additionally proves transfer through the half-unit relaxation using actual integer rows. Actual construction/coverage of the dyadic cells and oracle implementations remain assumptions.

**Not verified in Lean:** the short version's imported CKHM coordinate/encoding estimates; finite cover construction and coverage; the chamber count (Lemma 2.3 short / 2.4 extended), incremental enumeration and bit complexity; the full equivalence in Remark 2.3; the parallel-family count; local oracle implementations; Corollary 1.3's compatible-grid construction and range lower bound; or the full running-time theorem. `ReflectingCells.lean` and `check_reflecting.py` are historical explorations and are not included in the checked suite.

## Running and interpreting the audit

Follow the root README's setup, then run `python3 verification/check_all.py` from the repository root. This uses Python's standard library only. Individual checks remain available:

```sh
python3 verification/lean/check_fptas_calculations.py
python3 verification/lean/check_sampled_markov.py
python3 verification/lean/check_line_restriction.py
python3 verification/lean/check_scaled_polynomial.py
```

To reuse an already compiled dependency tree with exactly the locked revisions:

```sh
python3 verification/check_all.py --packages-dir /absolute/path/to/.lake/packages
```

The scripts verify dependency Git revisions, compile the source, and use `#print axioms` for every theorem. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. A compiler failure, missing axiom report, `sorryAx` or other axiom makes the check fail. A normal `lake build` compiles the modules but does not replace this axiom audit.

Each module has a `*_verification_log.txt`. The aggregate command writes `last_run.json` with UTC time, manuscript/source/checker hashes, pinned toolchain, exit codes and overall success. This file is refreshed at the start, so an interrupted or failed run cannot leave a previous aggregate success as the current result. Logs are evidence for the recorded sources, not a substitute for rerunning the checker after edits.

If `elan` is missing, install elan and put its binaries on PATH. If packages or compiled imports are missing, run `lake exe cache get` inside `verification/lean`. If a revision differs, use a fresh checkout with the committed manifest, rather than changing the manifest to silence the check. The checker does not install dependencies or access the network itself.

With `--experiments`, the finite-instance script also runs and refreshes `experiments/results.json`. These tests enumerate small bounded domains using exact arithmetic; they do not prove the general theorem or its complexity.

## Review the accompanying draft

`python3 verification/make_review_draft.py` regenerates `reflecting_cells_fptas_review.tex` from the short submission source. Blue notes mark conditional Lean coverage; amber notes identify human-review obligations. The review copy is not a submission layout or a certification of the whole paper. See `verification/reference_audit.txt` for the reference audit and its remaining limitations.

`python3 verification/check_all.py --check-record` checks whether the successful audit record still matches the current drafts and checked sources; it does not rerun Lean. Run the full check after any mathematical changes.

## Mixed-integer interface details

The current reduction uses `rounded_barycentric_weights` and `rounded_segment_weights` with nonnegative input weights, sum one, and a distinguished weight at least 1/(r+1). These assumptions come from Caratheodory and choosing a largest weight. The actual ceiling construction and residual convex weights are conclusions. `rounded_grid_coordinate` proves an integer numerator over k*Delta assuming integer scaled vertex coordinates. `unit_interval_markov_error` applies the mean value theorem to a polynomial with an explicit classical Markov hypothesis on [0,1]. `markov_grid_transfer` assumes a grid point with the established objective-error bound and a grid-solver guarantee, then derives the final range-relative error. The whole geometric reduction is not packaged as a single Lean theorem: the reader must check assembly, convex membership, integral-slice scaling, and complexity. The previous Lipschitz/range-gap transfer lemmas remain as historical helpers. ScaledPolynomial continues to verify polynomial substitution, integer coefficients, support/degree, feasible-set bijection, and encoding bounds.

## Scaled-polynomial interface

For a finite variable type and a finite set I of the continuous coordinates, `weight I a` is the sum of the exponents in I. `scaled f I Q D` assigns monomial a the integer coefficient `f.coeff a * Q^(D - weight I a)`. The degree hypothesis ensures the subtraction does not truncate for any supported monomial. `eval_scaled` evaluates this integer polynomial in the reals and proves the substitution identity for arbitrary real coordinates. `integer_representation` packages existence, support, degree bound and the identity. The results include the zero and constant polynomials, no continuous coordinates, and all continuous coordinates. Nonzero Q suffices algebraically; the grid reduction uses positive Q.

## Feasible-set and encoding interfaces

`encode` multiplies coordinates in I by Q, while `decode` divides them by Q; other coordinates are unchanged. `grid_coordinates` proves this means exactly Q^{-1} Z on I and Z elsewhere. For integral A,b and positive integer Q, `scaledRow` leaves columns in I unchanged and multiplies other columns by Q; the scaled right-hand side is Q*b. The row identity and two inverse identities give a bijection of the actual feasible sets, including empty sets and degenerate polytopes. This does not construct the compatible denominator supplied by DHKW.

`bitSize c = 1 + Nat.size c.natAbs` counts one sign bit and the magnitude bits. `bitSize_eq_clog` proves the natural ceiling-log formula, without invoking real logarithms. For every coefficient, `bitSize(c') <= bitSize(c) + D*Nat.size(abs(Q))`. Summing over the unchanged support gives coefficient payload growth at most `support.card * D * Nat.size(abs(Q))`. This yields the usual O(D log(Q+1)) growth per coefficient. The scaled matrix and right-hand-side lengths are now checked as described below. The asymptotic translation and arithmetic costs remain outside Lean; rational row normalization is checked below.

### Scaled constraint encoding

`bitSize_mul`, `scaledRow_bits`, and `scaled_rhs_bits` prove that each scaled matrix entry and right-hand side gains at most `Nat.size Q.natAbs` bits. `scaled_row_payload` sums over a row, including its right-hand side. `scaled_constraints_payload` sums over all rows, giving an increase at most `m*(d+1)*Nat.size Q.natAbs`. `scaled_constraints_encoding` includes any unchanged dimension/list metadata. This uses an explicit dense encoding with one sign bit plus binary magnitude for every integer entry (including zero); it does not claim a bound for arbitrary compressed encodings. The algebraic size bounds hold for every integer Q; the feasible-set equivalence separately requires Q > 0. Rational row denominator clearing is now checked below. Constructing the compatible grid denominator Q and arithmetic operation costs remain unverified.

### Rational constraint normalization

The twelve additional results in `ScaledPolynomial` construct `commonDen v` as the product of the positive rational denominators of a finite vector and `clearedEntry v i` as its numerator times the exact quotient. `commonDen_pos`, `denominator_dvd`, and `clearedEntry_real` verify positivity, divisibility and the real scaling identity. `size_prod_le`, `commonDen_bits`, `clearedEntry_bits`, and `cleared_payload` bound the denominator and integer-entry bit lengths. `rationalRow` includes the right-hand side as the `none` coordinate; `cleared_row_iff`, `cleared_system_iff`, and `cleared_domain_iff` preserve the inequality system, also under any additional domain restriction (in particular integer or mixed-integer feasibility). `cleared_payload_quadratic` gives at most `L*(L+2)` integer payload for a row of rational payload L; `cleared_matrix_payload` sums these bounds. Rational payload is the sum of signed numerator lengths and positive denominator magnitude lengths. These results do not certify the cost of computing products/divisions, or rational polynomial objective normalization as an actual polynomial construction. The latter is distinct from the already verified grid-scaled integer polynomial.

### Determinant-based coordinates and slacks (Lemma 2.1)

Nine results in `ScaledPolynomial` cover the numerical proof. `determinant_bound` expands an actual real determinant and proves `abs(det B) <= d! * C^d` from entry bounds. `factorial_power_bound` proves the strict bound with `coordinateExponent d tau = d*(tau + Nat.clog 2 (d+1)) + 2`. `integer_denominator_gap` proves that a nonzero integer denominator has magnitude at least one. `cramer_coordinate_bound` takes the Cramer ratio as an explicit hypothesis and derives the coordinate bound. `convex_coordinate_bound` handles arbitrary finite convex combinations, including zero weights. `slack_magnitude_bound`, `slack_power_bound`, and `dyadic_slack_bound` prove nonnegativity and the strict upper slack bound with `slackExponent d tau = tau + coordinateExponent d tau + Nat.clog 2 (d+1) + 2`. `represented_point_bounds` composes these results from Cramer data for vertices and a convex representation of the point, giving both coordinate and feasible-row slack bounds.

The determinant estimate itself is proved, not assumed. The geometric existence of independent active constraints, the resulting Cramer representation, and the convex-hull representation of a bounded polyhedron remain explicit external inputs. Coefficient bounds `abs(a) <= 2^tau` are hypotheses; the translation from the manuscript's real logarithm/ceiling notation to natural `Nat.clog` and the choice of tau is not formalized. Arithmetic complexity and enumeration of vertices are not certified.

The extended manuscript uses a single exponent Phi = (d+1)*(tau+Nat.clog 2 (d+1))+4. `unified_exponent_eq` proves it equals the earlier slack exponent; `unified_point_bounds` gives both coordinate and slack bounds with this common exponent. The sharper coordinate exponent is retained only as an internal proof helper. The original input encoding size remains varphi.

### Short-version imported CKHM bound

The short manuscript replaces its former coordinate/slack lemma with a paragraph citing the proof of CHKM Theorem 2.1, p.29. Their per-inequality size is bounded by (d+1)*(tau+3), including the right-hand side, and the short version uses Phi = 5*d^2*(d+1)*(tau+3)+2. The cited estimates apply to vertices of the integer hull and extend by linearity to all integer feasible points. CHKM's doubled shifted rows have twice our shifted slack. The one-dimensional case is handled directly. The resulting Phi remains O(d^3*(tau+1)), so the asymptotic complexity is unchanged.

This imported bound and its encoding translation remain human-review obligations. Lean's determinant and unified-exponent theorems continue to concern the sharper extended-version proof; they do not certify the new short-version Phi. The extended manuscript and its detailed proof are unchanged by this citation revision.
