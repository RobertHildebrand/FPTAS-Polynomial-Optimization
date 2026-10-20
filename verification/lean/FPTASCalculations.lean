import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Algebraic steps in reflecting_cells_fptas.tex. Analytic, geometric, and
oracle estimates are hypotheses, not axioms. This is not a full FPTAS proof. -/
namespace FPTASCalculations

theorem interval_width {a b u v T : ℝ}
    (hw : b - a ≤ a / T) (hu : a ≤ u ∧ u ≤ b)
    (hv : a ≤ v ∧ v ≤ b) : |v - u| ≤ a / T := by
  rw [abs_le]
  constructor <;> linarith

theorem slack_extrapolation {a s u v t T : ℝ} (hT : 0 < T)
    (hs : a ≤ s) (hw : |v - u| ≤ a / T) (ht : |t| ≤ T) :
    0 ≤ s + t * (v - u) := by
  have hp : |t * (v - u)| ≤ a := by
    rw [abs_mul]
    calc
      |t| * |v - u| ≤ T * (a / T) :=
        mul_le_mul ht hw (abs_nonneg _) (le_of_lt hT)
      _ = a := by field_simp
  have hn := neg_abs_le (t * (v - u))
  linarith

theorem sampled_sup_algebra {W R c : ℝ} (hW : 0 ≤ W)
    (hc : c ≤ 1 / 2) (h : W ≤ R / 2 + c * W) : W ≤ R := by
  have := mul_le_mul_of_nonneg_right hc hW
  nlinarith

theorem second_difference_transfer {pminus pzero pplus B : ℝ}
    (hmin : pzero ≤ pminus)
    (hsecond : pplus + pminus - 2 * pzero ≤ B) :
    pplus - pzero ≤ B := by
  linarith

theorem refinement_error {D ell eps : ℝ} (hD : 0 ≤ D) (heps : 0 < eps)
    (hell : 0 < ell) (hsize : D / Real.sqrt eps ≤ ell) :
    D ^ 2 / ell ^ 2 ≤ eps := by
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsq : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt heps.le
  have hm : D ≤ ell * Real.sqrt eps := (div_le_iff₀ hs).1 hsize
  have hpow := mul_self_le_mul_self hD hm
  apply (div_le_iff₀ (sq_pos_of_pos hell)).2
  nlinarith [hpow]

theorem local_comparison {F h : ℝ → ℝ} {best y optimum eta beta : ℝ}
    (hselect : F best ≤ F y) (hlocal : h y ≤ h optimum + eta)
    (hresidual : (F y - h y) - (F optimum - h optimum) ≤ beta) :
    F best - F optimum ≤ eta + beta := by
  linarith

theorem uniform_model_error {Fy Fx hy hx delta eta : ℝ}
    (hyerr : |Fy - hy| ≤ delta) (hxerr : |Fx - hx| ≤ delta)
    (hlocal : hy ≤ hx + eta) : Fy - Fx ≤ 2 * delta + eta := by
  rw [abs_le] at hyerr hxerr
  linarith

theorem nonnegative_maximization {value fmin fmax eps : ℝ}
    (hmin : 0 ≤ fmin) (heps : 0 ≤ eps)
    (herr : fmax - value ≤ eps * (fmax - fmin)) :
    (1 - eps) * fmax ≤ value := by
  nlinarith [mul_nonneg heps hmin]


/- The actual natural-number ceiling used by the algorithm. -/
theorem ceiling_refinement {D : ℕ} {eps : ℝ} (hD : 0 < D) (heps : 0 < eps) :
    let ell : ℕ := max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊
    0 < ell ∧ D ^ 2 ≤ ell ∧ (D : ℝ) ^ 2 / (ell : ℝ) ^ 2 ≤ eps := by
  dsimp
  have hl : 0 < max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ :=
    lt_of_lt_of_le (pow_pos hD _) (le_max_left _ _)
  refine ⟨hl, le_max_left _ _, refinement_error (Nat.cast_nonneg D) heps ?_ ?_⟩
  · exact_mod_cast hl
  · exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊))

/- A finite candidate set, indexed comparison regions, and sound local outputs.
The oracle inequality is stated pointwise, avoiding conventions for inf ∅. -/
theorem cover_solve_select {α ι : Type*} (X : Set α) (C R : ι → Set α)
    (F : α → ℝ) (h : ι → α → ℝ) (eta beta : ι → ℝ)
    (Y : Finset α) (optimum : α) (cstar : ι)
    (hopt : optimum ∈ X) (hminimum : ∀ x ∈ X, F optimum ≤ F x)
    (hcell : optimum ∈ C cstar)
    (hfeasible : ∀ y ∈ Y, y ∈ X)
    (horacle : ∀ c, (∃ x ∈ X, x ∈ C c) →
      ∃ y ∈ Y, y ∈ R c ∧ ∀ x ∈ X, x ∈ C c → h c y ≤ h c x + eta c)
    (hresidual : ∀ y ∈ R cstar,
      (F y - h cstar y) - (F optimum - h cstar optimum) ≤ beta cstar) :
    ∃ best ∈ Y, best ∈ X ∧ (∀ y ∈ Y, F best ≤ F y) ∧
      0 ≤ F best - F optimum ∧ F best - F optimum ≤ eta cstar + beta cstar := by
  obtain ⟨y, hy, hry, hlocal⟩ := horacle cstar ⟨optimum, hopt, hcell⟩
  obtain ⟨best, hb, hselect⟩ := Y.exists_min_image F ⟨y, hy⟩
  have hbest := hfeasible best hb
  refine ⟨best, hb, hbest, hselect, sub_nonneg.2 (hminimum best hbest), ?_⟩
  have hs := hselect y hy
  have hl := hlocal optimum hopt hcell
  have hr := hresidual y hry
  linarith

/- Empty output is equivalent to infeasibility, under coverage and a complete,
sound candidate oracle. No claim is made about implementing that oracle. -/
theorem empty_candidates_iff {α ι : Type*} (X : Set α) (C : ι → Set α)
    (Y : Finset α) (hcover : ∀ x ∈ X, ∃ c, x ∈ C c)
    (hfeasible : ∀ y ∈ Y, y ∈ X)
    (hcomplete : ∀ c, (∃ x ∈ X, x ∈ C c) → Y.Nonempty) :
    Y = ∅ ↔ X = ∅ := by
  constructor
  · intro hY
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    obtain ⟨c, hc⟩ := hcover x hx
    obtain ⟨y, hy⟩ := hcomplete c ⟨x, hx, hc⟩
    simpa [hY] using hy
  · intro hX
    apply Finset.eq_empty_iff_forall_notMem.2
    intro y hy
    have := hfeasible y hy
    simpa [hX] using this

/- Range-relative representative selection, with no surrogate optimization.
Only the representative in the optimal cell needs the assumed error bound. -/
theorem representative_range_guarantee {α : Type*} (X : Set α)
    (Y : Finset α) (f : α → ℝ) (optimum : α) (fmax eps : ℝ)
    (hminimum : ∀ x ∈ X, f optimum ≤ f x)
    (hfeasible : ∀ y ∈ Y, y ∈ X)
    (hrepresentative : ∃ y ∈ Y,
      f y - f optimum ≤ eps * (fmax - f optimum)) :
    ∃ best ∈ Y, best ∈ X ∧ (∀ y ∈ Y, f best ≤ f y) ∧
      0 ≤ f best - f optimum ∧
      f best - f optimum ≤ eps * (fmax - f optimum) := by
  obtain ⟨y, hy, herr⟩ := hrepresentative
  obtain ⟨best, hb, hselect⟩ := Y.exists_min_image f ⟨y, hy⟩
  have hf := hfeasible best hb
  refine ⟨best, hb, hf, hselect, sub_nonneg.2 (hminimum best hf), ?_⟩
  have := hselect y hy
  linarith


/- Linear constraint rows give the slack progression identity by linearity. -/
theorem linear_slack_progression {V : Type*} [AddCommGroup V] [Module ℝ V]
    (a : V →ₗ[ℝ] ℝ) (b : ℝ) (x y : V) (t : ℝ) :
    b - a (x + t • (y - x)) =
      (b - a x) + t * ((b - a y) - (b - a x)) := by
  simp only [map_add, map_smul, map_sub, smul_eq_mul]
  ring

/- All rows, including constant-slack boundary faces, are checked.
No feasibility of the extrapolated point is assumed. -/
theorem reflecting_cell_progression {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    (A : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (x y : V) (T t : ℝ)
    (hT : 0 < T) (ht : |t| ≤ T)
    (hcell : ∀ i,
      (0 ≤ b i - A i x ∧ b i - A i y = b i - A i x) ∨
      ∃ lo hi : ℝ, hi - lo ≤ lo / T ∧
        (lo ≤ b i - A i x ∧ b i - A i x ≤ hi) ∧
        (lo ≤ b i - A i y ∧ b i - A i y ≤ hi)) :
    ∀ i, A i (x + t • (y - x)) ≤ b i := by
  intro i
  have hs : 0 ≤ b i - A i (x + t • (y - x)) := by
    rw [linear_slack_progression]
    rcases hcell i with ⟨hpos, heq⟩ | ⟨lo, hi, hw, hx, hy⟩
    · simpa [heq] using hpos
    · exact slack_extrapolation hT hx.1 (interval_width hw hx hy) ht
  linarith

/- Any selected coordinates can be required to be integral. Thus this includes
pure integer, mixed-integer, and continuous spaces (all, some, or no indices). -/
theorem mixed_integer_progression {J : Type*} (I : Set J) (x y : J → ℝ) (k : ℤ)
    (hx : ∀ j ∈ I, ∃ z : ℤ, x j = z)
    (hy : ∀ j ∈ I, ∃ z : ℤ, y j = z) :
    ∀ j ∈ I, ∃ z : ℤ, (x + (k : ℝ) • (y - x)) j = z := by
  intro j hj
  obtain ⟨u, hu⟩ := hx j hj
  obtain ⟨v, hv⟩ := hy j hj
  refine ⟨u + k * (v - u), ?_⟩
  simp [hu, hv]

/- This is the discrete slack gap used when discarding (0,1) strips. -/
theorem integer_slack_gap (s : ℤ) (hs : 0 ≤ s) :
    s = 0 ∨ (1 : ℝ) ≤ (s : ℝ) := by
  by_cases hz : s = 0
  · exact Or.inl hz
  · right
    have : (1 : ℤ) ≤ s := by omega
    exact_mod_cast this

/-- The actual delta and compatible grid multiplier satisfy the grid theorem's
resolution condition; Delta itself is supplied by the integral scaling theorem. -/
theorem compatible_grid_parameters {eps rho K B : ℝ} {dc Delta : ℕ}
    (heps : 0 < eps) (hrho : 0 < rho) (hK : 0 < K) (hB : 0 < B)
    (hdc : 0 < dc) (hDelta : 0 < Delta) :
    let delta := eps * rho / (2 * K)
    let m : ℕ := ⌈2 * (dc : ℝ) * B / delta⌉₊
    let Q := Delta * m
    0 < delta ∧ 0 < Q ∧ Delta ∣ Q ∧
      2 * (dc : ℝ) * B / delta ≤ (m : ℝ) ∧
      K * delta = eps * rho / 2 := by
  dsimp
  have hd : 0 < eps * rho / (2 * K) := div_pos (mul_pos heps hrho) (by positivity)
  have ha : 0 < 2 * (dc : ℝ) * B / (eps * rho / (2 * K)) := by positivity
  have hc := Nat.le_ceil (2 * (dc : ℝ) * B / (eps * rho / (2 * K)))
  have hm : 0 < ⌈2 * (dc : ℝ) * B / (eps * rho / (2 * K))⌉₊ := by
    exact_mod_cast (lt_of_lt_of_le ha hc)
  refine ⟨hd, Nat.mul_pos hDelta hm, dvd_mul_right _ _, hc, ?_⟩
  field_simp

/-- Positive objective rescaling preserves the range-relative guarantee. -/
theorem positive_scaling_transfer {a b c u eps scale : ℝ}
    (hs : 0 < scale)
    (h : scale * u - scale * a ≤ eps * (scale * b - scale * c)) :
    u - a ≤ eps * (b - c) := by
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith [h]

/-- Single-grid reduction. The literature supplies a nearby feasible grid point
and Lipschitz estimate; the grid solver supplies its own range-relative error.
Both the positive-range and constant-objective cases are proved. -/
theorem mixed_integer_grid_transfer {α : Type*} [PseudoMetricSpace α]
    (S G : Set α) (f : α → ℝ) (xmin gmin gmax answer : α)
    (fmax eps rho K : ℝ)
    (heps : 0 < eps) (hrho : 0 < rho) (hK : 0 < K)
    (hsub : G ⊆ S) (hx : xmin ∈ S)
    (hmin : ∀ z ∈ S, f xmin ≤ f z) (hmax : ∀ z ∈ S, f z ≤ fmax)
    (hgmin : gmin ∈ G) (hgmax : gmax ∈ G) (ha : answer ∈ G)
    (hgridmin : ∀ z ∈ G, f gmin ≤ f z)
    (hrange : fmax = f xmin ∨ rho ≤ fmax - f xmin)
    (hnear : ∃ z ∈ G, dist z xmin ≤ eps * rho / (2 * K))
    (hlipschitz : ∀ z ∈ G, |f z - f xmin| ≤ K * dist z xmin)
    (hsolver : f answer - f gmin ≤ (eps / 2) * (f gmax - f gmin)) :
    answer ∈ S ∧ 0 ≤ f answer - f xmin ∧
      f answer - f xmin ≤ eps * (fmax - f xmin) := by
  have has := hsub ha
  refine ⟨has, sub_nonneg.mpr (hmin answer has), ?_⟩
  rcases hrange with hz | hp
  · have haU := hmax answer has
    rw [hz] at haU
    rw [hz]
    nlinarith [hmin answer has]
  · obtain ⟨z, hz, hd⟩ := hnear
    have hn : f z - f xmin ≤ K * (eps * rho / (2 * K)) :=
      (le_abs_self _).trans ((hlipschitz z hz).trans
        (mul_le_mul_of_nonneg_left hd (le_of_lt hK)))
    have hgm := hgridmin z hz
    have hminG := hmin gmin (hsub hgmin)
    have hmaxG := hmax gmax (hsub hgmax)
    have hid : K * (eps * rho / (2 * K)) = eps * rho / 2 := by field_simp
    rw [hid] at hn
    have hbudget := mul_le_mul_of_nonneg_left hp (le_of_lt heps)
    have hgridrange : f gmax - f gmin ≤ fmax - f xmin := by linarith
    have hhalf := mul_le_mul_of_nonneg_left hgridrange (show 0 ≤ eps / 2 by positivity)
    linarith

/-- The reduction still holds when the grid solver reports its guarantee for
Q^D times the original objective, as in denominator clearing in the draft. -/
theorem scaled_mixed_integer_grid_transfer {α : Type*} [PseudoMetricSpace α]
    (S G : Set α) (f : α → ℝ) (xmin gmin gmax answer : α)
    (fmax eps rho K Q : ℝ) (D : ℕ) (hQ : 0 < Q)
    (heps : 0 < eps) (hrho : 0 < rho) (hK : 0 < K)
    (hsub : G ⊆ S) (hx : xmin ∈ S)
    (hmin : ∀ z ∈ S, f xmin ≤ f z) (hmax : ∀ z ∈ S, f z ≤ fmax)
    (hgmin : gmin ∈ G) (hgmax : gmax ∈ G) (ha : answer ∈ G)
    (hgridmin : ∀ z ∈ G, f gmin ≤ f z)
    (hrange : fmax = f xmin ∨ rho ≤ fmax - f xmin)
    (hnear : ∃ z ∈ G, dist z xmin ≤ eps * rho / (2 * K))
    (hlipschitz : ∀ z ∈ G, |f z - f xmin| ≤ K * dist z xmin)
    (hsolver : Q^D * f answer - Q^D * f gmin ≤
      (eps / 2) * (Q^D * f gmax - Q^D * f gmin)) :
    answer ∈ S ∧ 0 ≤ f answer - f xmin ∧
      f answer - f xmin ≤ eps * (fmax - f xmin) := by
  apply mixed_integer_grid_transfer S G f xmin gmin gmax answer fmax eps rho K
    heps hrho hK hsub hx hmin hmax hgmin hgmax ha hgridmin hrange hnear hlipschitz
  exact positive_scaling_transfer (pow_pos hQ D) hsolver

/-- A complete same-slice grid approximation preserves nonemptiness. -/
theorem grid_nonempty_iff {α : Type*} (S G : Set α) (hsub : G ⊆ S)
    (hgrid : ∀ x ∈ S, ∃ y ∈ G, True) : G.Nonempty ↔ S.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hsub hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, _⟩ := hgrid x hx
    exact ⟨y, hy⟩

/-- Upward rounding, with no coefficient- or coordinate-dependent constant. -/
theorem ceil_weight_bounds (a k : ℝ) (hk : 0 < k) :
    a ≤ (⌈k*a⌉ : ℝ) / k ∧ (⌈k*a⌉ : ℝ) / k ≤ a + 1/k := by
  constructor
  · exact (le_div_iff₀ hk).2 (by simpa [mul_comm] using Int.le_ceil (k*a))
  · apply (div_le_iff₀ hk).2
    have h := Int.ceil_lt_add_one (k*a)
    have he : (a+1/k)*k = k*a+1 := by field_simp
    rw [he]
    exact le_of_lt h

/-- Round all but a largest barycentric coordinate upwards. -/
theorem rounded_barycentric_weights {r : ℕ} (a : Fin r → ℝ) (a0 k : ℝ)
    (hk : 0 < k) (ha : ∀ i, 0 ≤ a i)
    (hs : a0 + ∑ i, a i = 1) (hlarge : 1 ≤ (r+1 : ℝ)*a0)
    (hsize : (r : ℝ)*(r+1) ≤ k) :
    let mu := fun i => (⌈k*a i⌉ : ℝ)/k
    let mu0 := 1-∑ i, mu i
    let t := (r : ℝ)*(r+1)/k
    0 ≤ t ∧ t ≤ 1 ∧ 0 ≤ mu0 ∧
    (1-t)*a0 ≤ mu0 ∧ (∀ i, 0 ≤ mu i ∧ (1-t)*a i ≤ mu i) := by
  dsimp
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have ht0 : 0 ≤ (r : ℝ)*(r+1)/k := div_nonneg (by positivity) (le_of_lt hk)
  have ht1 : (r : ℝ)*(r+1)/k ≤ 1 := (div_le_iff₀ hk).2 (by simpa using hsize)
  have ha0 : 0 ≤ a0 := by nlinarith
  have hsum : (∑ i, (⌈k*a i⌉ : ℝ)/k) ≤ (∑ i, a i) + (r : ℝ)/k := by
    calc
      _ ≤ ∑ i, (a i + 1/k) := Finset.sum_le_sum (fun i _ => (ceil_weight_bounds (a i) k hk).2)
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  have hprod : (r : ℝ)/k ≤ ((r : ℝ)*(r+1)/k)*a0 := by
    have h := mul_le_mul_of_nonneg_left hlarge hr
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hk).2 (by nlinarith)
  have hmu0 : (1-(r : ℝ)*(r+1)/k)*a0 ≤ 1-∑ i, (⌈k*a i⌉ : ℝ)/k := by nlinarith
  refine ⟨ht0, ht1, le_trans (mul_nonneg (sub_nonneg.2 ht1) ha0) hmu0, hmu0, ?_⟩
  intro i
  have hi := (ceil_weight_bounds (a i) k hk).1
  exact ⟨le_trans (ha i) hi, le_trans (by nlinarith [mul_nonneg ht0 (ha i)]) hi⟩

/-- Dominating barycentric weights give a feasible-segment representation. -/
theorem barycentric_segment {r : ℕ} (a b : Fin r → ℝ) (t : ℝ)
    (ht : 0 < t) (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1)
    (hdom : ∀ i, (1-t)*a i ≤ b i) :
    let w := fun i => (b i-(1-t)*a i)/t
    (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
    (∀ i, b i = (1-t)*a i+t*w i) := by
  dsimp
  refine ⟨fun i => div_nonneg (sub_nonneg.2 (hdom i)) (le_of_lt ht), ?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hb, ha]
    field_simp; ring
  · intro i; field_simp; ring

/-- The actual rounded barycenter has denominator k*Delta coordinatewise. -/
theorem rounded_grid_coordinate {r : ℕ} (a : Fin r → ℝ)
    (v : Fin r → ℤ) (v0 : ℤ) (k Delta : ℕ)
    (hk : k ≠ 0) (hDelta : Delta ≠ 0) :
    (1-∑ i, (⌈(k:ℝ)*a i⌉ : ℝ)/(k:ℝ)) * ((v0:ℝ)/Delta) +
      ∑ i, ((⌈(k:ℝ)*a i⌉ : ℝ)/(k:ℝ))*((v i:ℝ)/Delta) =
    (((k:ℤ)-∑ i, ⌈(k:ℝ)*a i⌉)*v0 + ∑ i, ⌈(k:ℝ)*a i⌉*v i : ℤ) /
      ((k:ℝ)*Delta) := by
  push_cast
  rw [← Finset.sum_div]
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div]
  field_simp

/-- Ceiling choice of grid multiplier gives the half-error budget. -/
theorem markov_grid_multiplier (D r eps : ℝ)
    (hD : 1 ≤ D) (hr : 1 ≤ r) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    let k : ℝ := ⌈4*D^2*r*(r+1)/eps⌉
    0 < k ∧ r*(r+1) ≤ k ∧ 2*D^2*(r*(r+1)/k) ≤ eps/2 := by
  dsimp
  have hceil := Int.le_ceil (4*D^2*r*(r+1)/eps)
  have hnum : 0 < 4*D^2*r*(r+1) := by positivity
  have hk : 0 < (⌈4*D^2*r*(r+1)/eps⌉ : ℝ) := lt_of_lt_of_le (div_pos hnum heps) hceil
  have hmul := (div_le_iff₀ heps).1 hceil
  have hrr : 0 < r*(r+1) := by positivity
  have hD2 : 1 ≤ D^2 := by nlinarith
  have hbase : r*(r+1) ≤ 4*D^2*r*(r+1) := by nlinarith
  have hepk := mul_le_of_le_one_left (le_of_lt hk) heps1
  refine ⟨hk, by nlinarith, ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hk).2
  nlinarith

/-- A range-normalized segment Markov bound controls discretization error. -/
theorem markov_segment_error (p : ℝ → ℝ) (D t R eps : ℝ)
    (hR : 0 ≤ R) (hbudget : 2*D^2*t ≤ eps/2)
    (hmarkov : |p t-p 0| ≤ 2*D^2*t*R) :
    |p t-p 0| ≤ (eps/2)*R := by
  exact hmarkov.trans (mul_le_mul_of_nonneg_right hbudget hR)

/-- Grid transfer needs no positive range-gap or coefficient Lipschitz bound. -/
theorem markov_grid_transfer {α : Type*} (S G : Set α) (f : α → ℝ)
    (xmin gmin gmax answer : α) (fmax eps : ℝ)
    (heps : 0 ≤ eps) (hsub : G ⊆ S) (hx : xmin ∈ S)
    (hmin : ∀ z ∈ S, f xmin ≤ f z) (hmax : ∀ z ∈ S, f z ≤ fmax)
    (hgmin : gmin ∈ G) (hgmax : gmax ∈ G) (ha : answer ∈ G)
    (hgridmin : ∀ z ∈ G, f gmin ≤ f z)
    (hnear : ∃ y ∈ G, |f y-f xmin| ≤ (eps/2)*(fmax-f xmin))
    (hsolver : f answer-f gmin ≤ (eps/2)*(f gmax-f gmin)) :
    answer ∈ S ∧ 0 ≤ f answer-f xmin ∧ f answer-f xmin ≤ eps*(fmax-f xmin) := by
  obtain ⟨y, hy, herr⟩ := hnear
  have hymin := hgridmin y hy
  have hyerr := (le_abs_self (f y-f xmin)).trans herr
  have hgm := hmin gmin (hsub hgmin)
  have hgM := hmax gmax (hsub hgmax)
  have hprod := mul_le_mul_of_nonneg_left (show f gmax-f gmin ≤ fmax-f xmin by linarith) (show 0 ≤ eps/2 by positivity)
  exact ⟨hsub ha, sub_nonneg.2 (hmin answer (hsub ha)), by linarith⟩

/-- The upward-rounded weights admit explicit residual convex weights. -/
theorem rounded_segment_weights {r : ℕ} (a : Fin r → ℝ) (a0 k : ℝ)
    (hr : 0 < r) (hk : 0 < k) (ha : ∀ i, 0 ≤ a i)
    (hs : a0+∑ i, a i = 1) (hlarge : 1 ≤ (r+1 : ℝ)*a0)
    (hsize : (r : ℝ)*(r+1) ≤ k) :
    let mu := fun i => (⌈k*a i⌉ : ℝ)/k
    let mu0 := 1-∑ i, mu i
    let t := (r : ℝ)*(r+1)/k
    ∃ w0 : ℝ, ∃ w : Fin r → ℝ,
      0 ≤ w0 ∧ (∀ i, 0 ≤ w i) ∧ w0+∑ i, w i = 1 ∧
      mu0 = (1-t)*a0+t*w0 ∧ (∀ i, mu i = (1-t)*a i+t*w i) := by
  dsimp
  let t : ℝ := (r : ℝ)*(r+1)/k
  let mu := fun i => (⌈k*a i⌉ : ℝ)/k
  have ht : 0 < t := by dsimp [t]; positivity
  obtain ⟨_, _, _, h0, hi⟩ := rounded_barycentric_weights a a0 k hk ha hs hlarge hsize
  refine ⟨(1-∑ i, mu i-(1-t)*a0)/t, fun i => (mu i-(1-t)*a i)/t, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (sub_nonneg.2 h0) (le_of_lt ht)
  · intro i; exact div_nonneg (sub_nonneg.2 (hi i).2) (le_of_lt ht)
  · change (1-∑ i, mu i-(1-t)*a0)/t + (∑ i, (mu i-(1-t)*a i)/t) = 1
    have hsum : (∑ i, (mu i-(1-t)*a i)/t) = ((∑ i, mu i)-(1-t)*(∑ i, a i))/t := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum, ← add_div]
    apply (div_eq_one_iff_eq (ne_of_gt ht)).2
    nlinarith [hs]
  · change 1-∑ i, mu i = (1-t)*a0+t*((1-∑ i, mu i-(1-t)*a0)/t)
    rw [mul_div_cancel₀ _ (ne_of_gt ht)]
    ring
  · intro i
    change mu i = (1-t)*a i+t*((mu i-(1-t)*a i)/t)
    rw [mul_div_cancel₀ _ (ne_of_gt ht)]
    ring

/-- A barycentric segment identity holds in every coordinate. -/
theorem barycentric_coordinate_segment {r : ℕ} (a b w v : Fin r → ℝ)
    (a0 b0 w0 v0 t : ℝ)
    (h0 : b0 = (1-t)*a0+t*w0) (hi : ∀ i, b i = (1-t)*a i+t*w i) :
    b0*v0+∑ i, b i*v i =
      (1-t)*(a0*v0+∑ i, a i*v i)+t*(w0*v0+∑ i, w i*v i) := by
  rw [h0]
  simp_rw [hi, add_mul]
  rw [Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- Both sides of the grid multiplier bound, including rounding overhead. -/
theorem markov_grid_multiplier_bounds (D r eps : ℝ) :
    4*D^2*r*(r+1)/eps ≤ (⌈4*D^2*r*(r+1)/eps⌉ : ℝ) ∧
    (⌈4*D^2*r*(r+1)/eps⌉ : ℝ) < 4*D^2*r*(r+1)/eps+1 := by
  exact ⟨Int.le_ceil _, Int.ceil_lt_add_one _⟩

end FPTASCalculations


