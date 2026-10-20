# What Lean verifies

The current audit covers **31 + 13 + 15 + 64 + 26 + 47 + 21 + 39 = 256 theorems**. Where numbering differs, both short and extended numbers are given; theorem names are the stable identifiers. Every result is conditional on its displayed Lean hypotheses. An axiom audit does not discharge those hypotheses.

## Scope after the symmetrization revision (October 17, 2026)

The audit now covers the strengthened `D^2 / ell^2` estimate and the actual refinement `max(D^2, ceil(D / sqrt(epsilon)))`, including `ell >= D^2` and the error inequality. The even-part representation is constructed and proved, not assumed. The sharper symmetric-difference factor `4 * floor(D/2)^2` is also verified. Representative bounds, including the multivariate selection theorem, use the new estimate. Finite-instance experiments now use the revised refinement and error budget.

The conditional one-grid error transfer, compatible-grid parameter arithmetic, positive objective scaling and grid nonemptiness are now checked. The current Markov-based reduction does not use a range lower bound. Its geometric and polynomial assembly is now checked, conditional on published slice data and the scaled solver guarantee; full algorithmic complexity remains outside the formalization. The manuscript, source and checker hashes in `last_run.json` identify the audited development.

## Shifted closed chambers (October 19, 2026)

Both manuscripts now use shifted right-hand sides b+1/2 and closed full-dimensional chambers inside Q. LineRestriction adds six verified theorems: `integer_row_value` constructs an integer row value from actual integer coefficients; `integer_half_shift` proves the scalar integer gap; `shifted_feasible_iff` identifies the two integer feasible sets; `shifted_slack_positive` proves the half-unit margin; `shifted_slack_integral_progression` returns the integer samples from the relaxation to the original set; and `shifted_slack_cover_guarantee` assembles the final error guarantee from closed interval-width hypotheses.

The shift applies after the mixed-integer grid reduction, not directly to mixed-integer constraints. Coverage by chamber closures is now proved in CoverAssembly. The rational descriptions, compression to two bounds per row and rounded integer membership tests are now proved. The LP interior criterion is now proved. Correctness and attainment of a returned LP optimum and operation costs remain external; the geometric insertion bound is now proved in ChamberInsertion. The chamber-count arithmetic and scalar threshold coverage are now checked in CoverArithmetic. The older unshifted slack theorems remain checked auxiliary results; their zero-slack branches are no longer needed by the manuscript's construction. Determinant proofs still concern the original coordinate bounds; the added half-unit in the upper slack estimate is accounted for in the manuscript, not by a new determinant theorem.

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
| Corollary 1.3: Markov-based grid reduction | FPTASCalculations: `rounded_barycentric_weights`, `rounded_segment_weights`, `barycentric_coordinate_segment`, `rounded_grid_coordinate`, `markov_grid_multiplier`, `markov_grid_multiplier_bounds`, `markov_grid_transfer`; SampledMarkov: `unit_interval_markov_error` | Verifies ceiling rounding, residual convex weights, coordinatewise segment/grid identities, multiplier bounds and error composition. CoverAssembly now assembles these into `mixed_integer_reduction`; classical Markov, integral-slice scaling, Caratheodory data and solver/cost hypotheses remain external. |

| Corollary 1.3: scaled polynomial | [ScaledPolynomial](lean/ScaledPolynomial.lean): `weight_le`, `coefficient`, `support_scaled`, `degree_bound`, `degree_preserved`, `monomial_substitution`, `eval_scaled`, `integer_representation` | Constructs an actual integer-coefficient MvPolynomial. Proves evaluation equals Q^D f(u/Q,z), identical support and degree for nonzero integer Q, and degree at most D. Assumes only nonzero Q and the input degree bound; no substitution identity or integrality is assumed. Feasible-set identification and polynomial coefficient bit lengths are proved below. Scaled matrix/right-hand-side bit lengths are proved below; their construction cost and full runtime remain external. |

| Corollary 1.3: scaled feasible set | [ScaledPolynomial](lean/ScaledPolynomial.lean): `decode_encode`, `encode_decode`, `row_identity`, `grid_coordinates`, `scaled_feasible_iff`, `grid_feasible_iff`, `feasible_bijection` | Defines integer scaled rows: keep continuous columns, multiply the other columns and right-hand side by positive Q. Proves an actual bijection with the compatible-grid feasible set. Grid existence/construction is not assumed by these identities and is not proved here. |
| Corollary 1.3: coefficient binary lengths | [ScaledPolynomial](lean/ScaledPolynomial.lean): `bitSize_eq_clog`, `size_mul_le`, `size_mul_pow_le`, `coefficient_bits`, `coefficient_payload` | Proves signed bit length is 1 + Nat.clog 2 (abs(c)+1), the per-coefficient bound by bitSize(c)+D*size(abs(Q)), and summed coefficient-payload growth. No asymptotic runtime or cost of constructing Q is asserted. |

| Current shifted construction and Theorem 1.1 | [LineRestriction](lean/LineRestriction.lean): `integer_row_value`, `integer_half_shift`, `shifted_feasible_iff`, `shifted_slack_positive`, `shifted_slack_integral_progression`, `shifted_slack_cover_guarantee` | Checks integer row evaluation, the half-unit relaxation, positive slack, and the final guarantee from closed shifted intervals. The auxiliary theorem assumes coverage; CoverAssembly proves it for the actual slack-chamber closures. Oracle completeness, extrema and Markov remain hypotheses; the geometric insertion and chamber-count bound are now proved in ChamberInsertion; enumeration implementation remains external. |

## The boundary of the formalization

`MarkovBound` in [SampledMarkov.lean](lean/SampledMarkov.lean) is a conjunction of two propositions passed as hypotheses, not a new Lean axiom. `CenteredMarkovBound D T` is the classical derivative estimate on [-T,T] with factor D²/T. `IntervalMarkovBound (D/2) 0 (T²)` is the classical estimate on [0,T²] with factor 2 floor(D/2)²/T². Both are applications of the same established inequality, with different degrees and intervals. No even-part identity, degree bound or symmetrization error estimate is included in the assumptions.

The proof chain is: relative slack widths imply feasible progressions; affine substitution gives a univariate polynomial; sampled Markov control gives an error near an optimum; finite selection preserves that guarantee. The new `LineRestriction.certified_cover_guarantee` assembles the analytic error estimate and actual refinement with an abstract finite cover. Coverage, sound/complete representatives, feasible progressions, an attained minimizer, global bounds, and the classical Markov inequalities are explicit hypotheses. The auxiliary `slack_cover_guarantee` wires the rowwise slack hypotheses and coordinate integrality into this theorem through `slack_integral_progression`. Progression feasibility is a conclusion, not an input. The current `shifted_slack_cover_guarantee` additionally proves transfer through the half-unit relaxation using actual integer rows. `CoverAssembly.chamber_approximation` now supplies actual slack-threshold chamber closures, proves coverage (including boundary points), derives relative widths, and invokes that guarantee. It assumes proper rows, continuity, the CHKM slack bound, complete feasible representatives, extrema and Markov. Oracle implementations remain external.

**Not verified in Lean:** the published CHKM estimates and the per-row encoding convention (their numerical translation is now checked); the LP solver and attainment/correctness of its reported optimum (the interior criterion, coverage, widths, rational descriptions and compression are now proved); incremental enumeration implementation and bit complexity; the full equivalence in Remark 2.3; the parallel-family count; local oracle implementations; published integral-slice/Caratheodory data for Corollary 1.3 (the current proof does not require a range lower bound); or the full running-time theorem. `ReflectingCells.lean` and `check_reflecting.py` are historical explorations and are not included in the checked suite.

## Running and interpreting the audit

Follow the root README's setup, then run `python3 verification/check_all.py` from the repository root. This uses Python's standard library only. Individual checks remain available:

```sh
python3 verification/lean/check_fptas_calculations.py
python3 verification/lean/check_sampled_markov.py
python3 verification/lean/check_line_restriction.py
python3 verification/lean/check_scaled_polynomial.py
python3 verification/lean/check_cover_arithmetic.py
python3 verification/lean/check_cover_assembly.py
python3 verification/lean/check_chamber_insertion.py
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

CoverArithmetic now verifies the numerical translation to the short-version Phi conditional on the published estimates and the stated per-row encoding bound. The geometric source facts remain explicit hypotheses. ScaledPolynomial's determinant and unified-exponent results continue to concern the sharper extended-version proof.

### Mixed-integer complexity calculation

Ten additional ScaledPolynomial results check the new bound.
- `continuous_basis_count`, `continuous_basis_power_bound`: candidate r-row basis count and its power bound.
- `integer_basis_determinant_size`: determinant magnitude-to-bit bound using the checked Leibniz estimate (given an integer determinant value and entry magnitude bounds).
- `basis_lcm_spec`, `basis_lcm_size`: positivity, divisibility, and encoding length of the actual finite lcm of nonzero determinant magnitudes.
- `mixed_grid_size`: binary length of Q=k*Delta.
- `mixed_grid_polynomial_size`, `mixed_scaled_input_size`: polynomial absorption of basis count, determinant sizes, multiplier sizes, and aggregate payload.
- `mixed_runtime_composition`, `mixed_runtime_exponent`: composition of preprocessing and integer-solver cost bounds and explicit absorption into a constant multiple of d(r+1).

The runtime theorems assume the cost bounds; they do not verify basis enumeration, gcd/lcm implementation, or Kannan's algorithm. The translation of normalization into total input size, and the connection of each abstract payload/cost parameter to the concrete algorithm, remain human-review obligations. The actual bound on k's encoding is now verified below. This is a verification of the complexity calculation under explicit inputs, not of the complete algorithm.

### Further encoding and interval checks

- `integer_slack_interval`, `shifted_integer_slack_interval`: exact equivalence between real closed intervals and ceiling/floor bounds on integer slacks, including the half-unit shift.
- `rational_grid_multiplier_le`, `rational_grid_multiplier_size`: for positive integers a,b and epsilon=a/b, the actual ceiling k has binary magnitude length at most 3+2 size(D)+size(r)+size(r+1)+size(b).
- `full_scaled_input_payload`: combines the actual scaled constraint and polynomial payloads and the denominator of epsilon/2. Unchanged exponent/list metadata is included explicitly. It does not formalize a concrete file serialization or the operation costs.

Still check the normalization-to-global-input-size translation, the choice and accounting of serialization metadata, chamber enumeration and endpoint sizes, and preprocessing/solver cost hypotheses. Convex membership assembly and the external geometric and Markov results remain as described above.

## CHKM translation, threshold coverage, and chamber arithmetic (October 20, 2026)

[CoverArithmetic.lean](lean/CoverArithmetic.lean) adds 26 theorems, with a separate checker and axiom audit.

- `chkm_encoding_translation` assumes the published vertex coordinate and doubled shifted-slack estimates with per-row size F and F <= (d+1)(tau+3), and proves the strict upper bounds using `chkmPhi`. `chkm_coordinate_absorption` and `chkm_slack_absorption` handle the constants, including d=2. `chkm_convex_bounds` assumes a convex representation and checks numerical extension, including the half-unit lower bound. `one_dimensional_bounds` handles d=1 from coefficient bounds and the elementary interval coordinate bound. Source theorems, the serialization convention, and existence of these representations are not proved.
- `thresholds` is the actual finite set: final endpoint 2^Phi and all 2^k/4*(1+j/ell), k<Phi+2 and j<ell. This is the manuscript's indexing shifted by two. `dyadic_band`, `refined_band`, `threshold_mem`, and `upper_threshold_mem` construct covering endpoints; `threshold_width` proves the relative width. `threshold_coverage` covers every real slack in [1/4,2^Phi), and `rowwise_threshold_coverage` assembles those intervals over the rows. `threshold_count` proves cardinality at most (Phi+2)*ell+1. This does not identify the interval boxes with full-dimensional chamber closures or implement their enumeration.
- `chamber_recurrence` proves Pascal's recurrence for the binomial sum, and `chamber_power_bound` proves R_d(H)<=(1+H)^d. `insertion_count_bound` assumes the geometric insertion recurrence and proves the binomial upper bound by induction. `oracle_and_lp_counts` assumes the one-query-per-chamber and two-tests-per-stage bounds. `hyperplane_count`, `hyperplane_linear_refinement`, and `refinement_query_counts` substitute the actual hyperplane bound and yield constants times ell^d and ell^(d+1). The epsilon substitution uses the earlier refinement results; no new asymptotic runtime or oracle implementation is certified.

Run all eight modules with `python3 verification/check_all.py`; run the new module with `python3 verification/lean/check_cover_arithmetic.py`. The standalone checker rebuilds ScaledPolynomial first. Both commands accept `--packages-dir` for the pinned compiled dependencies.

## Assembled cover and mixed-integer guarantees

[CoverAssembly.lean](lean/CoverAssembly.lean) contains **47 theorems**. Run its standalone audit with `python3 verification/lean/check_cover_assembly.py`; this rebuilds the six modules through CoverAssembly in dependency order. The aggregate check includes it automatically.

- `interval_cover`, `interval_widths`, and `interval_approximation` construct a finite family of generated interval cells and prove its approximation guarantee. This intermediate family is not asserted to have an efficient enumeration: the chamber results below provide the geometric bridge.
- `avoid_hyperplanes_dense`, `strictRegion_union`, and `retained_chamber_cover` prove that every point of an open region lies in the closure of a nonempty strict sign region for finitely many proper hyperplanes. The point itself need not avoid the hyperplanes.
- `closure_in_interval`, `retained_slack_chamber_cover`, `slackInterior_open`, and `slack_chamber_narrow` specialize to the actual slack thresholds. Each retained closure lies in a generated narrow interval cell. `chamber_approximation` connects these closures directly to the polynomial approximation theorem: **cover and relative widths are conclusions**, not hypotheses. The open outer region is `1/4 < slack < 2^Phi`; feasible integer points lie there by the half-unit shift and the assumed upper slack bound. Empty strict regions have empty closures. Properness excludes zero rows, whose preprocessing remains external. Continuity of the row maps is explicit. The rational closed-inequality representation is now proved below; chamber enumeration is not implemented.
- `barycenter_mem` and `rounded_barycenter_segment` derive convex feasibility and the actual residual segment from rounded weights. `polynomial_segment_error` applies Markov to the genuine line restriction. `rounded_mixed_grid`, `natural_grid_budget`, and `mixed_rounding_near` give a feasible grid point with the half-error budget.
- `SliceData` records the published compatible-slice and Caratheodory inputs: a convex slice, vertices on the Delta grid, fixed integer coordinates, nonnegative barycentric weights with largest distinguished weight, and the representation of the optimizer. It is a structure of hypotheses, not a new axiom.
- `mixed_integer_reduction` combines this data with the actual scaled integer polynomial and scaled feasible set, and returns feasibility and range-relative error for the decoded answer. The scaled solver's guarantee, attained grid extrema, global objective bounds, positive dimension/degree and Markov remain explicit assumptions. Zero-degree and zero-continuous-dimension cases are handled separately in the paper, not by this positive-parameter theorem. The published existence of SliceData, oracle implementation and runtime are not proved by this assembly.

All new declarations are included in the transitive axiom audit. No custom axioms or `sorry` are permitted. The formalization verifies mathematical implications, not the execution of the manuscript's enumeration and optimization subroutines.

## Rational descriptions of retained chamber closures

Fourteen additional results in CoverAssembly close the representation gap:

- `closure_strict_linear`: a nonempty strict linear system has closure equal to the same system with weak inequalities. The proof moves from any weakly feasible point toward a strictly feasible witness along an open segment. Nonemptiness is essential; this theorem makes no claim for a discarded empty strict region.
- `threshold_rational`, `endpoint_rational`, and `endpointRat_cast`: all generated endpoints have rational values, with their real coercions checked.
- `chamberMatrix` and `chamberRhs`: actual rational coefficients for the two outer bounds and each signed threshold inequality. `rationalRow_continuous` proves continuity, rather than assuming it for this representation. `chamber_strict_description` identifies the strict system with the previously defined slack chamber. `chamber_closure_rational_description` proves the exact set equality for every retained chamber.
- `lowerSlacks` and `upperSlacks` include the outer bounds and all appropriate signed thresholds. Their finite rational maximum and minimum give `lowerSlack` and `upperSlack`. `compressed_slack_description` and `chamber_closure_compressed` prove equality with the two bounds per original row, hence at most 2m scalar inequalities. This is exact equality, not just containment in an interval box.
- `chamber_integer_tests`: an integer vector belongs to that closure exactly when its original integer slack lies between ceil(lowerSlack - 1/2) and floor(upperSlack - 1/2). Thus the representation is connected to the rounded feasibility tests, not merely to an abstract polyhedron.

These results do not prove endpoint bit-length bounds or the enumeration implementation and its running time. The LP interior criterion is now proved below. They do not yet prove that the two selected endpoints are consecutive in the sorted threshold list; their equality with the full halfspace system and the previously proved relative-width containment suffice for the checked approximation argument. The rational endpoint selector is noncomputable in Lean; its value and rationality are proved, not a verified implementation of threshold generation.

## LP test for nonempty interior

Ten more theorems in CoverAssembly verify the common-margin test used by the enumerator:

- `interior_linear_system`: for finitely many continuous, nonzero linear rows, the interior of the weak system is exactly the strict system. The proof uses openness of each nonzero linear functional; zero rows must be removed first.
- `strict_iff_positive_margin`: strict feasibility at x is equivalent to a common margin delta > 0 with delta <= 1 and L_i(x) + delta <= a_i for every row. The margin is the minimum of 1 and the finitely many positive slacks. An empty row list is handled by the inserted value 1.
- `margin_feasible_iff`: the margin LP is feasible exactly when the original weak system is nonempty (delta = 0 suffices). Thus an infeasible LP certifies an empty candidate cell.
- `interior_iff_positive_margin` connects these results. `margin_optimum_test` proves that a given feasible optimal pair has positive objective exactly when the weak system has nonempty interior. Feasibility and global optimality of that pair are explicit hypotheses; the theorem does not implement an LP solver or prove existence/attainment of an optimum.
- `chamber_rows_proper` derives properness of every signed rational row from properness of the original rows. `chamber_margin_test` identifies nonempty interior with a nonempty strict chamber, even for candidates that will be discarded. `chamber_optimum_test` applies the LP criterion to the actual full rational chamber system.
- `compressed_linear_description` and `compressed_optimum_test` apply the same test to the compressed system with two inequalities per original row, using its actual rational right-hand sides. The criterion concerns the unrounded chamber used in enumeration, not the later inward-rounded integer-feasibility polytope.

The geometric insertion/count bound is now proved below. Remaining algorithmic obligations include exact LP solver correctness and attainment, enumeration implementation, endpoint bit lengths and operation costs. All new theorem declarations are included in the same transitive axiom audit.

## Geometric insertion and the chamber bound

[ChamberInsertion.lean](lean/ChamberInsertion.lean) adds **21 theorems** and removes the geometric recurrence as an assumption for the chamber-count result. Its standalone audit is `python3 verification/lean/check_chamber_insertion.py`; it rebuilds all seven modules and audits every theorem in the new module. The aggregate audit includes it.

- `patterns` is the finite set of strict sign vectors realized in a domain. `sign_cell_convex` proves convexity of every such region in a convex domain. `patterns_mono` shows that restriction of the domain cannot increase the number.
- `crossing_witness` constructs the point where a segment between opposite sides meets the inserted hyperplane. `split_patterns_subset_section` preserves the old sign vector at this point: identity on sign vectors is the injection from split chambers to realized regions on the hyperplane.
- `insertion_inequality` proves the geometric count from finite union/intersection cardinalities. `patterns_cons`, `patterns_head_card` and `patterns_succ_card` identify the two children with the actual sign vectors after insertion.
- `section_patterns` translates the induced arrangement to the kernel of the inserted linear functional. `section_convex` preserves convexity of the domain. `kernel_dimension` proves the one-dimension drop using rank-nullity and surjectivity of a nonzero real linear functional.
- `zero_insertion` handles constant restrictions without increasing the count. Thus repeated or parallel hyperplanes, lower-dimensional domains, and restricted rows that vanish do not require a general-position hypothesis.
- `arrangement_count_bound` proves the binomial upper bound by induction on the number of rows, for any finite-dimensional real vector space and convex domain. **Neither geometric insertion nor dimension reduction is a hypothesis.** `finite_arrangement_bound` removes the Fin indexing restriction.
- `closed_chamber_count` bounds the finite image of closures of all realized sign regions. `slackInterior_convex` proves convexity of the actual shifted-slack outer domain. Finally, `shifted_chamber_count` bounds the actual retained closed family by R_d(m*((Phi+2)*ell+1)), using the verified threshold cardinality. This counts the finite family mathematically; it does not implement its incremental enumeration.

The earlier `CoverArithmetic.insertion_count_bound` remains a checked abstract recurrence lemma, but its geometric hypothesis is no longer a gap in the new chamber-count proof. The parallel-family refinement is still not formalized. LP/ILP implementations, per-stage operation counts and the full runtime theorem remain separate obligations.


## Threshold and cell encoding (October 20, 2026)

[CellEncoding.lean](lean/CellEncoding.lean) contains **39 theorems**. Run `python3 verification/lean/check_cell_encoding.py` (with the same optional `--packages-dir`); the aggregate checker includes it. The standalone checker rebuilds all eight modules and audits the new module.

The convention is `bitSize(z) = 1 + size(abs(z))` and `ratBits(q) = bitSize(q.num) + 1 + size(q.den)`, using the reduced numerator and positive denominator. Dimension and list metadata are separate from these dense coefficient payloads.

- `reduced_components` and `reduced_bits` prove that reducing a rational fraction cannot increase its component lengths. `endpoint_fraction` gives every actual threshold a common denominator `4*ell` and a natural numerator at most `4*ell*2^Phi`; `endpoint_den_divides` proves reduced-denominator divisibility. `endpoint_bits` bounds its rational payload by `Phi + 2*size(ell) + 8`.
- `lower_endpoint` and `upper_endpoint` identify the selected compressed bounds with actual thresholds, so `compressed_endpoint_bits` and `endpoint_range` apply to them. `compressed_rhs_bits` includes the original right-hand side: at most `bitSize(b_i) + Phi + 4*size(ell) + 15`.
- `rational_cell_payload` bounds the actual compressed rational system by `2*m*(d*(tau+2)+tau+Phi+4*size(ell)+15)`, assuming signed input lengths at most tau. `margin_column_payload` adds four bits per original inequality for the common-margin coefficient 1. `margin_bound_rows_payload` checks the additional `6*d+15` bits for the two rows `-delta <= 0` and `delta <= 1` in d+1 variables. These are coefficient/RHS payloads, not solver running times or a particular serialization.
- `rounded_bits` bounds each half-shifted floor/ceiling by `Phi+2` bits, independently of ell. `rounded_rhs_bits` adds `bitSize(b_i)`. `rounded_matrix_bits` checks the unchanged signed matrix lengths.
- `rounded_system` and `chamber_integer_encoding` identify the encoded integer system with the previously proved integer membership test for a nonempty strict chamber's closure. `rounded_cell_payload` gives `2*m*(d*tau+tau+Phi+2)`; `rounded_cell_encoding` adds arbitrary unchanged metadata explicitly.

No bit-length bound above assumes the desired conclusion as an encoding hypothesis. Positivity of ell, the input entry bounds and, for the membership identification, nonemptiness of the strict chamber are explicit assumptions. Construction/serialization implementations, their arithmetic costs, LP/ILP algorithms, and the full runtime theorem remain unverified. The paper's polynomial absorption of these displayed bounds uses its existing parameter estimates.


### Complete LP queries and polynomial absorption

Twelve further results in `CellEncoding` assemble the encoding bound rather than assuming it. `lpMatrix` and `lpRhs` include the 2m compressed inequalities with a common margin column and the two inequalities bounding that margin; `lpObjective` maximizes the margin. `lpMetadata` describes a dense schema with signed-binary row and column counts, a length field for each augmented constraint row, the objective-vector length, and one maximization-direction bit. No particular file format or byte-level encoder is implemented.

`lp_encoding_identity` gives the complete query size as the compressed rational constraint payload plus `8*m + 9*d + 19 + lpMetadata(m,d)`, including the objective. `complete_lp_encoding` bounds that payload using the actual cell data. `lp_metadata_bound` proves the metadata bound `(2*m+2)*(d+3)+2*m+2*d+8`.

`refinement_size` proves, for positive natural D,a,q and epsilon=a/q, that the actual `max(D^2, ceil(D/sqrt(epsilon)))` has magnitude bit length at most `2*size(D)+size(q)`. This does not assume a bound on the refinement itself. `unary_degree_size` gives `size(D)<=phi` from the unary-degree bound `D<=phi`. `cleared_entry_input_bound` gives signed length at most `phi+1` for entries obtained by clearing a rational row whose payload is at most phi. `coefficient_log_bound` bounds the manuscript's natural ceiling-log parameter by `phi+1` when the maximum coefficient magnitude is less than `2^phi` and phi>0.

`chkm_phi_polynomial` proves `Phi<=42*(phi+1)^4` from d<=phi and tau<=phi+1. `lp_bound_polynomial` and `complete_lp_polynomial` then give **complete LP query size <=200*(phi+1)^5**. The latter uses the actual refinement and actual cell matrix, right-hand side, objective and metadata, with explicit bounds m,d<=phi, tau<=phi+1, normalized signed entry lengths<=phi+1, size(D),size(q)<=phi, and positive D,a,q. These are parameter-domination hypotheses, not an assumed polynomial bound on the query. The individual normalization, degree, logarithm and refinement bridges are proved separately; the extraction of all input parameters from a serialized manuscript instance is not implemented.

`rounded_cell_polynomial` gives the same conservative polynomial upper bound for the rounded integer cell, using the LP metadata as an overestimate. Unlike the rational LP query, this conclusion needs no bound on the refinement's size. Neither polynomial bound claims a verified construction cost, solver runtime, or complete FPTAS implementation.
