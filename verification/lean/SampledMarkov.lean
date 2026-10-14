import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic
import Mathlib.Analysis.Convex.Deriv

namespace SampledMarkov

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
    (fun t ht => by simpa [Polynomial.deriv, Real.norm_eq_abs] using hmarkov p hdeg W hW t ht)
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



/-- The symmetric second-difference estimate, derived from Mathlib convexity.
No Taylor or integration identity is assumed. -/
theorem second_difference_bound (p : Polynomial ℝ) (B : ℝ)
    (hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, p.derivative.derivative.eval t ≤ B) :
    p.eval 1 + p.eval (-1) - 2 * p.eval 0 ≤ B := by
  let g : Polynomial ℝ := Polynomial.C (B / 2) * Polynomial.X ^ 2 - p
  have hg : ∀ t, g.derivative.derivative.eval t = B - p.derivative.derivative.eval t := by
    intro t
    simp [g, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have hd : deriv (fun t => g.eval t) = (fun t => g.derivative.eval t) := by
    funext t
    exact g.deriv
  have hdd : deriv (deriv (fun t => g.eval t)) =
      (fun t => g.derivative.derivative.eval t) := by
    rw [hd]
    funext t
    exact g.derivative.deriv
  have hconv : ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (fun t => g.eval t) := by
    apply convexOn_of_deriv2_nonneg' (convex_Icc _ _) g.differentiableOn
    · rw [hd]
      exact g.derivative.differentiableOn
    · intro t ht
      change 0 ≤ deriv (deriv (fun t => g.eval t)) t
      rw [hdd]
      change 0 ≤ g.derivative.derivative.eval t
      rw [hg]
      exact sub_nonneg.2 (hbound t ht)
  have hm := hconv.2 (show (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  norm_num [g, smul_eq_mul] at hm
  linarith

/-- The manuscript's sampled Markov lemma, conditional only on the classical
scaled Markov inequality. All remaining analytic and algebraic steps are proved. -/
theorem sampled_markov {D T : ℕ} (hT : 1 ≤ T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D) {a b : ℝ}
    (hsample : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      a ≤ p.eval (k : ℝ) ∧ p.eval (k : ℝ) ≤ b)
    (hmin : p.eval 0 ≤ p.eval (-1)) :
    p.eval 1 - p.eval 0 ≤ (D : ℝ)^4 / (T : ℝ)^2 * (b-a) := by
  let q := p - Polynomial.C ((a+b)/2)
  have hqdeg : q.natDegree ≤ D :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hdeg (by simp))
  have hqsample : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      |q.eval (k : ℝ)| ≤ (b-a)/2 := by
    intro k hk
    simp only [q, Polynomial.eval_sub, Polynomial.eval_C]
    rw [abs_le]
    constructor <;> linarith [(hsample k hk).1, (hsample k hk).2]
  have hW := sampled_sup_bound (by omega : 0 < T) hDT hmarkov q hqdeg hqsample
  have hdW := hmarkov q hqdeg (b-a) hW
  have hddeg : q.derivative.natDegree ≤ D :=
    (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hqdeg)
  have hddW := hmarkov q.derivative hddeg _ hdW
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      p.derivative.derivative.eval t ≤ (D : ℝ)^4 / (T : ℝ)^2 * (b-a) := by
    intro t ht
    have h := hddW t (by constructor <;> linarith [ht.1, ht.2])
    have heq : (D : ℝ)^2 / T * ((D : ℝ)^2 / T * (b-a)) =
        (D : ℝ)^4 / (T : ℝ)^2 * (b-a) := by ring
    rw [heq] at h
    have hder : q.derivative.derivative = p.derivative.derivative := by simp [q]
    rw [hder] at h
    exact (le_abs_self _).trans h
  have hsecond := second_difference_bound p _ hb
  linarith


/-- Feasible integer samples and global optimality imply the representative
error. Polynomial restriction and its degree bound are explicit hypotheses. -/
theorem representative_at_minimum {α : Type*} (X : Set α) (f : α → ℝ)
    (xmin y : α) (fmax : ℝ) {D T : ℕ} (hT : 1 ≤ T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (hy : y ∈ X) (hbounds : ∀ z ∈ X, f xmin ≤ f z ∧ f z ≤ fmax)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D)
    (hzero : p.eval 0 = f xmin) (hone : p.eval 1 = f y)
    (hprogression : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      ∃ z ∈ X, p.eval (k : ℝ) = f z) :
    0 ≤ f y - f xmin ∧
      f y - f xmin ≤ (D : ℝ)^4 / (T : ℝ)^2 * (fmax - f xmin) := by
  have hs : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      f xmin ≤ p.eval (k : ℝ) ∧ p.eval (k : ℝ) ≤ fmax := by
    intro k hk
    obtain ⟨z, hz, heq⟩ := hprogression k hk
    rw [heq]
    exact hbounds z hz
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hm := (hs (-1) (by constructor <;> norm_num <;> linarith)).1
  have hm' : p.eval 0 ≤ p.eval (-1) := by simpa [hzero] using hm
  have herr := sampled_markov hT hDT hmarkov p hdeg hs hm'
  refine ⟨sub_nonneg.2 (hbounds y hy).1, ?_⟩
  simpa [hzero, hone] using herr

/-- The corresponding maximum estimate is proved by applying the minimum
estimate to the negated objective and polynomial. -/
theorem representative_at_maximum {α : Type*} (X : Set α) (f : α → ℝ)
    (xmax y : α) (fmin : ℝ) {D T : ℕ} (hT : 1 ≤ T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (hy : y ∈ X) (hbounds : ∀ z ∈ X, fmin ≤ f z ∧ f z ≤ f xmax)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ D)
    (hzero : p.eval 0 = f xmax) (hone : p.eval 1 = f y)
    (hprogression : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      ∃ z ∈ X, p.eval (k : ℝ) = f z) :
    0 ≤ f xmax - f y ∧
      f xmax - f y ≤ (D : ℝ)^4 / (T : ℝ)^2 * (f xmax - fmin) := by
  have h := representative_at_minimum X (fun z => -f z) xmax y (-fmin)
    hT hDT hmarkov hy
    (fun z hz => ⟨neg_le_neg (hbounds z hz).2, neg_le_neg (hbounds z hz).1⟩)
    (-p) (by simpa using hdeg)
    (by simpa using congrArg Neg.neg hzero)
    (by simpa using congrArg Neg.neg hone) (by
      intro k hk
      obtain ⟨z, hz, heq⟩ := hprogression k hk
      exact ⟨z, hz, by simpa using congrArg Neg.neg heq⟩)
  simpa only [neg_sub_neg] using h

/-- Finite selection composed with the sampled Markov lemma. Only one
representative (in an optimum's cell) needs a feasible polynomial progression. -/
theorem select_representative {α : Type*} (X : Set α) (Y : Finset α)
    (f : α → ℝ) (xmin : α) (fmax : ℝ) {D T : ℕ} (hT : 1 ≤ T)
    (hDT : (D : ℝ)^2 ≤ T) (hmarkov : MarkovBound D T)
    (hfeasible : ∀ y ∈ Y, y ∈ X)
    (hbounds : ∀ z ∈ X, f xmin ≤ f z ∧ f z ≤ fmax)
    (hwitness : ∃ y ∈ Y, ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      p.eval 0 = f xmin ∧ p.eval 1 = f y ∧
      ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
        ∃ z ∈ X, p.eval (k : ℝ) = f z) :
    ∃ best ∈ Y, best ∈ X ∧ (∀ y ∈ Y, f best ≤ f y) ∧
      0 ≤ f best - f xmin ∧
      f best - f xmin ≤ (D : ℝ)^4 / (T : ℝ)^2 * (fmax - f xmin) := by
  obtain ⟨y, hy, p, hdeg, hzero, hone, hprog⟩ := hwitness
  have herr := representative_at_minimum X f xmin y fmax hT hDT hmarkov
    (hfeasible y hy) hbounds p hdeg hzero hone hprog
  obtain ⟨best, hb, hselect⟩ := Y.exists_min_image f ⟨y, hy⟩
  have hf := hfeasible best hb
  refine ⟨best, hb, hf, hselect, sub_nonneg.2 (hbounds best hf).1, ?_⟩
  have := hselect y hy
  linarith [herr.2]

end SampledMarkov


