import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic
import SampledMarkov

namespace LineRestriction

noncomputable def restrict {σ : Type*} (f : MvPolynomial σ ℝ) (x y : σ → ℝ) :
    Polynomial ℝ :=
  f.eval₂ Polynomial.C (fun i => Polynomial.C (x i) +
    Polynomial.C (y i - x i) * Polynomial.X)

theorem eval_restrict {σ : Type*} (f : MvPolynomial σ ℝ) (x y : σ → ℝ) (t : ℝ) :
    (restrict f x y).eval t = MvPolynomial.eval (fun i => x i + t * (y i - x i)) f := by
  classical
  simp [restrict, MvPolynomial.eval, MvPolynomial.eval₂_eq,
    Polynomial.eval_finsetSum, Polynomial.eval_prod, mul_comm]

theorem eval_zero {σ : Type*} (f : MvPolynomial σ ℝ) (x y : σ → ℝ) :
    (restrict f x y).eval 0 = MvPolynomial.eval x f := by
  simp [eval_restrict]

theorem eval_one {σ : Type*} (f : MvPolynomial σ ℝ) (x y : σ → ℝ) :
    (restrict f x y).eval 1 = MvPolynomial.eval y f := by
  simp [eval_restrict]

theorem degree_restrict {σ : Type*} (f : MvPolynomial σ ℝ) (x y : σ → ℝ) :
    (restrict f x y).natDegree ≤ f.totalDegree := by
  classical
  have ha : ∀ i, (Polynomial.C (x i) +
      Polynomial.C (y i - x i) * Polynomial.X).natDegree ≤ 1 := by
    intro i
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact (Polynomial.natDegree_mul_le).trans (by simp)
  rw [restrict, MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  apply le_trans Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_C, zero_add]
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  apply le_trans _ (MvPolynomial.le_totalDegree hs)
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ ≤ (Polynomial.C (x i) + Polynomial.C (y i - x i) * Polynomial.X).natDegree * s i :=
      by simpa [Nat.mul_comm] using (Polynomial.natDegree_pow_le (p :=
        Polynomial.C (x i) + Polynomial.C (y i - x i) * Polynomial.X) (n := s i))
    _ ≤ 1 * s i := Nat.mul_le_mul_right _ (ha i)
    _ = s i := one_mul _


/-- Actual multivariate polynomials now supply the degree-bounded restriction.
Only feasibility of the geometric progression and classical Markov remain inputs. -/
theorem multivariate_representative {σ : Type*} (f : MvPolynomial σ ℝ)
    (S : Set (σ → ℝ)) (x y : σ → ℝ) (fmax : ℝ) {D T : ℕ}
    (hdeg : f.totalDegree ≤ D) (hT : 1 ≤ T) (hDT : (D : ℝ)^2 ≤ T)
    (hmarkov : SampledMarkov.MarkovBound D T) (hy : y ∈ S)
    (hbounds : ∀ z ∈ S, MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧
      MvPolynomial.eval z f ≤ fmax)
    (hprogression : ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      (fun i => x i + (k : ℝ) * (y i - x i)) ∈ S) :
    0 ≤ MvPolynomial.eval y f - MvPolynomial.eval x f ∧
    MvPolynomial.eval y f - MvPolynomial.eval x f ≤
      (D : ℝ)^4 / (T : ℝ)^2 * (fmax - MvPolynomial.eval x f) := by
  apply SampledMarkov.representative_at_minimum S (fun z => MvPolynomial.eval z f)
    x y fmax hT hDT hmarkov hy hbounds (restrict f x y)
    ((degree_restrict f x y).trans hdeg) (eval_zero f x y) (eval_one f x y)
  intro k hk
  exact ⟨_, hprogression k hk, eval_restrict f x y (k : ℝ)⟩

/-- Finite candidate selection for an actual multivariate polynomial. -/
theorem multivariate_selection {σ : Type*} (f : MvPolynomial σ ℝ)
    (S : Set (σ → ℝ)) (Y : Finset (σ → ℝ)) (x : σ → ℝ) (fmax : ℝ) {D T : ℕ}
    (hdeg : f.totalDegree ≤ D) (hT : 1 ≤ T) (hDT : (D : ℝ)^2 ≤ T)
    (hmarkov : SampledMarkov.MarkovBound D T)
    (hfeasible : ∀ y ∈ Y, y ∈ S)
    (hbounds : ∀ z ∈ S, MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧
      MvPolynomial.eval z f ≤ fmax)
    (hwitness : ∃ y ∈ Y, ∀ k : ℤ, (k : ℝ) ∈ Set.Icc (-(T : ℝ)) T →
      (fun i => x i + (k : ℝ) * (y i - x i)) ∈ S) :
    ∃ best ∈ Y, best ∈ S ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f - MvPolynomial.eval x f ∧
      MvPolynomial.eval best f - MvPolynomial.eval x f ≤
        (D : ℝ)^4 / (T : ℝ)^2 * (fmax - MvPolynomial.eval x f) := by
  apply SampledMarkov.select_representative S Y (fun z => MvPolynomial.eval z f)
    x fmax hT hDT hmarkov hfeasible hbounds
  obtain ⟨y, hy, hprog⟩ := hwitness
  refine ⟨y, hy, restrict f x y, (degree_restrict f x y).trans hdeg,
    eval_zero f x y, eval_one f x y, ?_⟩
  intro k hk
  exact ⟨_, hprog k hk, eval_restrict f x y (k : ℝ)⟩

end LineRestriction

