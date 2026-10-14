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

theorem refinement_error {D ell eps : ℝ} (heps : 0 < eps)
    (hell : 0 < ell) (hsize : D ^ 2 / Real.sqrt eps ≤ ell) :
    D ^ 4 / ell ^ 2 ≤ eps := by
  have hs : 0 < Real.sqrt eps := Real.sqrt_pos.2 heps
  have hsq : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt (le_of_lt heps)
  have hm : D ^ 2 ≤ ell * Real.sqrt eps := (div_le_iff₀ hs).1 hsize
  have hn : 0 ≤ ell * Real.sqrt eps := le_of_lt (mul_pos hell hs)
  have hpow : (D ^ 2) ^ 2 ≤ (ell * Real.sqrt eps) ^ 2 := by
    nlinarith [sq_nonneg (ell * Real.sqrt eps - D ^ 2)]
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
theorem ceiling_refinement {D eps : ℝ} (hD : 0 < D) (heps : 0 < eps) :
    let ell : ℕ := ⌈D ^ 2 / Real.sqrt eps⌉₊
    0 < ell ∧ D ^ 4 / (ell : ℝ) ^ 2 ≤ eps := by
  dsimp
  have ht : 0 < D ^ 2 / Real.sqrt eps :=
    div_pos (sq_pos_of_pos hD) (Real.sqrt_pos.2 heps)
  have hl : 0 < ⌈D ^ 2 / Real.sqrt eps⌉₊ := Nat.ceil_pos.2 ht
  refine ⟨hl, refinement_error heps ?_ (Nat.le_ceil _)⟩
  exact_mod_cast hl

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

end FPTASCalculations


