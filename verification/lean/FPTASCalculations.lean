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

end FPTASCalculations


