import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
Core of the reflecting-cell approximation proof. Literature results are explicit
hypotheses, never axioms. Enumeration and bit complexity are outside this module.
-/
namespace ReflectingCells

/-- Scalar form of the slack calculation; allows any base point in the cell. -/
theorem slack_extrapolation {a T s u v t : ℝ}
    (hT : 0 ≤ T) (hs : a ≤ s) (hwidth : |v - u| ≤ a / T)
    (hTpos : 0 < T) (ht : |t| ≤ T) :
    0 ≤ s + t * (v - u) := by
  have hprod : |t * (v - u)| ≤ a := by
    rw [abs_mul]
    calc
      |t| * |v - u| ≤ T * (a / T) :=
        mul_le_mul ht hwidth (abs_nonneg _) hT
      _ = a := by field_simp
  have := neg_abs_le (t * (v - u))
  linarith

/-- A narrow positive interval supplies the requisite slack difference bound. -/
theorem interval_width {a b u v T : ℝ} (_hT : 0 < T)
    (hu : u ∈ Set.Ioo a b) (hv : v ∈ Set.Ioo a b)
    (hwidth : b - a ≤ a / T) : |v - u| ≤ a / T := by
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- An abstract slack representation covers rational polyhedra in any dimension.
The affine identity is the defining identity of a slack along a line. -/
theorem long_reflection {X I : Type*} (C : Set X) (slack : I → X → ℝ)
    (line : X → X → ℝ → X) (T : ℝ) (hT : 0 < T)
    (haff : ∀ i x y t, slack i (line x y t) =
      slack i x + t * (slack i y - slack i x))
    (hcell : ∀ i, (∃ a, 0 ≤ a ∧ ∀ x ∈ C, slack i x = a) ∨
      ∃ a b, b - a ≤ a / T ∧ ∀ x ∈ C, slack i x ∈ Set.Ioo a b)
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) {t : ℝ} (ht : |t| ≤ T) :
    ∀ i, 0 ≤ slack i (line x y t) := by
  intro i
  rw [haff]
  rcases hcell i with ⟨a, ha, hc⟩ | ⟨a, b, hw, hc⟩
  · rw [hc x hx, hc y hy]; simpa using ha
  · exact slack_extrapolation hT.le (hc x hx).1.le
      (interval_width hT (hc x hx) (hc y hy) hw) hT ht

/-- Classical scaled Markov inequality, in pointwise upper-bound form.
This is an explicit literature hypothesis; it is not asserted as a Lean axiom. -/
def MarkovBound (D : ℕ) (T : ℝ) : Prop :=
  ∀ (p : Polynomial ℝ), p.natDegree ≤ D → ∀ W : ℝ,
    (∀ t ∈ Set.Icc (-T) T, |p.eval t| ≤ W) →
    ∀ t ∈ Set.Icc (-T) T, |p.derivative.eval t| ≤ (D : ℝ)^2 / T * W

/-- Mean-value consequence of the classical derivative bound. -/
theorem markov_difference {D : ℕ} {T W : ℝ}
    (hmarkov : MarkovBound D T) (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D)
    (hW : ∀ t ∈ Set.Icc (-T) T, |p.eval t| ≤ W)
    {x y : ℝ} (hx : x ∈ Set.Icc (-T) T) (hy : y ∈ Set.Icc (-T) T) :
    |p.eval y - p.eval x| ≤ ((D : ℝ)^2 / T * W) * |y - x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun t => p.eval t)
    (fun t _ => p.differentiableAt)
    (fun t ht => by simpa using hmarkov p hdeg W hW t ht)
    (convex_Icc (-T) T) hx hy
  simpa [Real.norm_eq_abs] using h

/-- Rounding stays inside an interval with integer endpoints. -/
theorem nearest_integer (T : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (-(T : ℝ)) T) :
    ∃ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T ∧ |t - k| ≤ 1/2 := by
  refine ⟨round t, ?_, abs_sub_round t⟩
  have hr := abs_sub_round t
  rw [abs_le] at hr
  constructor
  · by_contra h
    have hk : round t ≤ -(T : ℤ) - 1 := by
      have : (round t : ℝ) < -(T : ℝ) := lt_of_not_ge h
      have : round t < -(T : ℤ) := by exact_mod_cast this
      omega
    have hk' : (round t : ℝ) ≤ -(T : ℝ) - 1 := by exact_mod_cast hk
    linarith [ht.1]
  · by_contra h
    have hk : (T : ℤ) + 1 ≤ round t := by
      have : (T : ℝ) < (round t : ℝ) := lt_of_not_ge h
      have : (T : ℤ) < round t := by exact_mod_cast this
      omega
    have hk' : (T : ℝ) + 1 ≤ (round t : ℝ) := by exact_mod_cast hk
    linarith [ht.2]

/-- Sample bounds imply a continuous bound for a centered polynomial.
The key absorption step is proved, including the zero-range case. -/
theorem sampled_sup_bound {D T : ℕ} (hT : 0 < T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (q : Polynomial ℝ) (hdeg : q.natDegree ≤ D) {R : ℝ}
    (hsample : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T → |q.eval (k : ℝ)| ≤ R/2) :
    ∀ t ∈ Set.Icc (-(T : ℝ)) T, |q.eval t| ≤ R := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by linarith : -(T : ℝ) ≤ T))
    q.continuous.abs.continuousOn
  let W := |q.eval u|
  have hW : ∀ t ∈ Set.Icc (-(T : ℝ)) T, |q.eval t| ≤ W := fun t ht => hmax ht
  obtain ⟨k, hk, hnear⟩ := nearest_integer T hu
  have hdiff := markov_difference hmarkov q hdeg hW hk hu
  have hcoef : 0 ≤ (D : ℝ)^2 / T * W :=
    mul_nonneg (div_nonneg (sq_nonneg _) hTr.le) (abs_nonneg _)
  have hdiff' : |q.eval u - q.eval (k : ℝ)| ≤ ((D : ℝ)^2 / T * W) / 2 := by
    calc
      _ ≤ ((D : ℝ)^2 / T * W) * |u - k| := hdiff
      _ ≤ ((D : ℝ)^2 / T * W) * (1/2) := mul_le_mul_of_nonneg_left hnear hcoef
      _ = _ := by ring
  have hratio : (D : ℝ)^2 / T ≤ 1 := (div_le_one hTr).mpr hDT
  have hmul : (D : ℝ)^2 / T * W ≤ W := by
    simpa using mul_le_mul_of_nonneg_right hratio (abs_nonneg (q.eval u))
  have htri : W ≤ |q.eval u - q.eval (k : ℝ)| + |q.eval (k : ℝ)| := by
    simpa [W] using abs_add_le (q.eval u - q.eval (k : ℝ)) (q.eval (k : ℝ))
  have hWR : W ≤ R := by linarith [hsample k hk]
  exact fun t ht => (hW t ht).trans hWR

/-- The central discrete Markov estimate used in the paper (T ≥ D² version). -/
theorem discrete_markov {D T : ℕ} (hT : 1 ≤ T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D) {a b : ℝ}
    (hsample : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      a ≤ p.eval (k : ℝ) ∧ p.eval (k : ℝ) ≤ b) :
    |p.eval 1 - p.eval 0| ≤ (D : ℝ)^2 / T * (b-a) := by
  let q := p - Polynomial.C ((a+b)/2)
  have hqdeg : q.natDegree ≤ D := by
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le hdeg (by simp))
  have hqsample : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      |q.eval (k : ℝ)| ≤ (b-a)/2 := by
    intro k hk
    simp only [q, Polynomial.eval_sub, Polynomial.eval_C]
    rw [abs_le]
    constructor <;> linarith [(hsample k hk).1, (hsample k hk).2]
  have hW := sampled_sup_bound (by omega : 0 < T) hDT hmarkov q hqdeg hqsample
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h := markov_difference hmarkov q hqdeg hW
    (x := 0) (y := 1) (by constructor <;> linarith) (by constructor <;> linarith)
  simpa [q] using h

/-- Abstract cell oscillation: line restriction and feasible integer progression
are explicit interfaces to the multivariate polynomial and lattice geometry. -/
theorem cell_oscillation {X : Type*} (f : X → ℝ) (S C : Set X)
    {D T : ℕ} (hT : 1 ≤ T) (hDT : (D : ℝ)^2 ≤ T)
    (hmarkov : MarkovBound D T) {a b : ℝ}
    (hbounds : ∀ z ∈ S, a ≤ f z ∧ f z ≤ b)
    (hrestriction : ∀ x ∈ C, ∀ y ∈ C,
      ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧ p.eval 0 = f x ∧ p.eval 1 = f y ∧
        ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T → ∃ z ∈ S, p.eval (k : ℝ) = f z)
    {x y : X} (hx : x ∈ C) (hy : y ∈ C) :
    |f y - f x| ≤ (D : ℝ)^2 / T * (b-a) := by
  obtain ⟨p, hp, hx0, hy1, hprog⟩ := hrestriction x hx y hy
  have h := discrete_markov hT hDT hmarkov p hp (a := a) (b := b) (by
    intro k hk
    obtain ⟨z, hz, heq⟩ := hprog k hk
    rw [heq]
    exact hbounds z hz)
  simpa [hx0, hy1] using h

/-- Representative guarantee, independent of the cover's construction or size. -/
theorem representative_guarantee {X I : Type*} (f : X → ℝ) (S : Set X)
    (C : I → Set X) (rep : I → X) {eps R : ℝ} {xmin best : X}
    (hmin : ∀ x ∈ S, f xmin ≤ f x) (hbest : best ∈ S)
    (hcover : ∃ i, xmin ∈ C i)
    (hrep : ∀ i, rep i ∈ C i)
    (hosc : ∀ i x y, x ∈ C i → y ∈ C i → |f y - f x| ≤ eps * R)
    (hselect : ∀ i, f best ≤ f (rep i)) :
    0 ≤ f best - f xmin ∧ f best - f xmin ≤ eps * R := by
  obtain ⟨i, hi⟩ := hcover
  have h := (abs_le.mp (hosc i xmin (rep i) hi (hrep i))).2
  constructor <;> linarith [hmin best hbest, hselect i]

/-- Optimizing any uniformly accurate local model incurs at most twice its error. -/
theorem model_minimization {X : Type*} (f h : X → ℝ) {x y : X} {eta : ℝ}
    (hx : |f x - h x| ≤ eta) (hy : |f y - h y| ≤ eta)
    (hopt : h y ≤ h x) : f y - f x ≤ 2 * eta := by
  rw [abs_le] at hx hy
  linarith [hx.1, hy.2]

/-- Cover-level Taylor/model guarantee; the error estimate and exact model
minimization are separate, visible hypotheses. -/
theorem model_cover_guarantee {X I : Type*} (f : X → ℝ) (S : Set X)
    (C : I → Set X) (model : I → X → ℝ) (candidate : I → X)
    {eps R eta : ℝ} {xmin best : X}
    (hmin : ∀ x ∈ S, f xmin ≤ f x) (hbest : best ∈ S)
    (hcover : ∃ i, xmin ∈ C i) (hcand : ∀ i, candidate i ∈ C i)
    (herr : ∀ i x, x ∈ C i → |f x - model i x| ≤ eta)
    (hopt : ∀ i x, x ∈ C i → model i (candidate i) ≤ model i x)
    (hselect : ∀ i, f best ≤ f (candidate i)) (hbudget : 2 * eta ≤ eps * R) :
    0 ≤ f best - f xmin ∧ f best - f xmin ≤ eps * R := by
  obtain ⟨i, hi⟩ := hcover
  have h := model_minimization f (model i) (herr i xmin hi)
    (herr i (candidate i) (hcand i)) (hopt i xmin hi)
  constructor <;> linarith [hmin best hbest, hselect i]

end ReflectingCells
