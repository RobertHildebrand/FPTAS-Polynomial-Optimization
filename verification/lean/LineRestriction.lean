import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic
import SampledMarkov
import FPTASCalculations

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
      (D : ℝ)^2 / (T : ℝ)^2 * (fmax - MvPolynomial.eval x f) := by
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
        (D : ℝ)^2 / (T : ℝ)^2 * (fmax - MvPolynomial.eval x f) := by
  apply SampledMarkov.select_representative S Y (fun z => MvPolynomial.eval z f)
    x fmax hT hDT hmarkov hfeasible hbounds
  obtain ⟨y, hy, hprog⟩ := hwitness
  refine ⟨y, hy, restrict f x y, (degree_restrict f x y).trans hdeg,
    eval_zero f x y, eval_one f x y, ?_⟩
  intro k hk
  exact ⟨_, hprog k hk, eval_restrict f x y (k : ℝ)⟩

/-- The draft's error guarantee, conditional on a finite reflecting cover and
complete feasible representatives. Construction and runtime are not asserted. -/
theorem certified_cover_guarantee {σ ι : Type*} (f : MvPolynomial σ ℝ)
    (S : Set (σ → ℝ)) (C : ι → Set (σ → ℝ)) (Y : Finset (σ → ℝ))
    (x : σ → ℝ) (fmax eps : ℝ) (D : ℕ)
    (hD : 0 < D) (heps : 0 < eps) (hdeg : f.totalDegree ≤ D)
    (hx : x ∈ S)
    (hbounds : ∀ z ∈ S, MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧
      MvPolynomial.eval z f ≤ fmax)
    (hcover : ∀ z ∈ S, ∃ c, z ∈ C c)
    (hfeasible : ∀ y ∈ Y, y ∈ S)
    (hcomplete : ∀ c, (∃ z ∈ S, z ∈ C c) → ∃ y ∈ Y, y ∈ C c)
    (hmarkov : SampledMarkov.MarkovBound D
      (max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊))
    (hreflect : ∀ c, ∀ u ∈ S, ∀ v ∈ S, u ∈ C c → v ∈ C c →
      ∀ k : ℤ, (k : ℝ) ∈ Set.Icc
        (-(max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ : ℝ))
        (max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ : ℝ) →
      (fun i => u i + (k : ℝ) * (v i - u i)) ∈ S) :
    ∃ best ∈ Y, best ∈ S ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f - MvPolynomial.eval x f ∧
      MvPolynomial.eval best f - MvPolynomial.eval x f ≤
        eps * (fmax - MvPolynomial.eval x f) := by
  obtain ⟨hpos, hlarge, herr⟩ := FPTASCalculations.ceiling_refinement hD heps
  obtain ⟨c, hc⟩ := hcover x hx
  obtain ⟨y, hy, hcy⟩ := hcomplete c ⟨x, hx, hc⟩
  have hlargeR : (D : ℝ)^2 ≤
      (max (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ : ℝ) := by
    exact_mod_cast hlarge
  obtain ⟨best, hb, hf, hs, hn, he⟩ := multivariate_selection f S Y x fmax
    hdeg hpos (by simpa only [Nat.cast_max, Nat.cast_pow] using hlargeR)
    (by simpa only [Nat.cast_max, Nat.cast_pow] using hmarkov) hfeasible hbounds
    ⟨y, hy, by simpa only [Nat.cast_max, Nat.cast_pow] using
      (hreflect c x hx y (hfeasible y hy) hc hcy)⟩
  refine ⟨best, hb, hf, hs, hn, he.trans ?_⟩
  exact mul_le_mul_of_nonneg_right herr (sub_nonneg.mpr (hbounds x hx).2)

/-- A linear feasible region with a specified subset of integral coordinates. -/
def linearIntegerSet {σ κ : Type*}
    (A : κ → (σ → ℝ) →ₗ[ℝ] ℝ) (b : κ → ℝ) (I : Set σ) : Set (σ → ℝ) :=
  {x | (∀ i, A i x ≤ b i) ∧ ∀ j ∈ I, ∃ z : ℤ, x j = z}

/-- Slack width and coordinate integrality together imply feasible progression
samples. Unlike certified_cover_guarantee, no progression is assumed. -/
theorem slack_integral_progression {σ κ : Type*}
    (A : κ → (σ → ℝ) →ₗ[ℝ] ℝ) (b : κ → ℝ) (I : Set σ)
    (x y : σ → ℝ) (T : ℝ) (k : ℤ) (hT : 0 < T)
    (hx : x ∈ linearIntegerSet A b I) (hy : y ∈ linearIntegerSet A b I)
    (hk : (k : ℝ) ∈ Set.Icc (-T) T)
    (hslacks : ∀ i,
      (0 ≤ b i - A i x ∧ b i - A i y = b i - A i x) ∨
      ∃ lo hi : ℝ, hi - lo ≤ lo / T ∧
        (lo ≤ b i - A i x ∧ b i - A i x ≤ hi) ∧
        (lo ≤ b i - A i y ∧ b i - A i y ≤ hi)) :
    (fun i => x i + (k : ℝ) * (y i - x i)) ∈ linearIntegerSet A b I := by
  constructor
  · exact FPTASCalculations.reflecting_cell_progression A b x y T k hT
      (abs_le.mpr hk) hslacks
  · exact FPTASCalculations.mixed_integer_progression I x y k hx.2 hy.2

/-- Final polynomial error guarantee on linear constraints with integral
coordinates. The geometric assumption is now the rowwise slack condition,
not the feasibility of the extrapolated samples. -/
theorem slack_cover_guarantee {σ ι κ : Type*} (f : MvPolynomial σ ℝ)
    (A : κ → (σ → ℝ) →ₗ[ℝ] ℝ) (b : κ → ℝ) (I : Set σ)
    (C : ι → Set (σ → ℝ)) (Y : Finset (σ → ℝ))
    (x : σ → ℝ) (fmax eps : ℝ) (D : ℕ)
    (hD : 0 < D) (heps : 0 < eps) (hdeg : f.totalDegree ≤ D)
    (hx : x ∈ linearIntegerSet A b I)
    (hbounds : ∀ z ∈ linearIntegerSet A b I, MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧
      MvPolynomial.eval z f ≤ fmax)
    (hcover : ∀ z ∈ linearIntegerSet A b I, ∃ c, z ∈ C c)
    (hfeasible : ∀ y ∈ Y, y ∈ linearIntegerSet A b I)
    (hcomplete : ∀ c, (∃ z ∈ linearIntegerSet A b I, z ∈ C c) → ∃ y ∈ Y, y ∈ C c)
    (hmarkov : SampledMarkov.MarkovBound D
      (max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊))
    (hslacks : ∀ c, ∀ u ∈ linearIntegerSet A b I,
      ∀ v ∈ linearIntegerSet A b I, u ∈ C c → v ∈ C c → ∀ i,
      (0 ≤ b i - A i u ∧ b i - A i v = b i - A i u) ∨
      ∃ lo hi : ℝ,
        hi - lo ≤ lo / (max (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ : ℝ) ∧
        (lo ≤ b i - A i u ∧ b i - A i u ≤ hi) ∧
        (lo ≤ b i - A i v ∧ b i - A i v ≤ hi)) :
    ∃ best ∈ Y, best ∈ linearIntegerSet A b I ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f - MvPolynomial.eval x f ∧
      MvPolynomial.eval best f - MvPolynomial.eval x f ≤
        eps * (fmax - MvPolynomial.eval x f) := by
  apply certified_cover_guarantee f (linearIntegerSet A b I) C Y x fmax eps D
    hD heps hdeg hx hbounds hcover hfeasible hcomplete hmarkov
  intro c u hu v hv huc hvc k hk
  apply slack_integral_progression A b I u v _ k _ hu hv hk
    (hslacks c u hu v hv huc hvc)
  have hp := (FPTASCalculations.ceiling_refinement hD heps).1
  have : (0 : ℝ) < (↑(max (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊) : ℝ) := by
    exact_mod_cast hp
  simpa only [Nat.cast_max, Nat.cast_pow] using this

/-- A constraint row constructed from actual integer coefficients. -/
def integerRow {σ : Type*} [Fintype σ] (a : σ → ℤ) : (σ → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ j, (a j : ℝ) * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]

/-- Integer coefficients and integer coordinates give an integer row value. -/
theorem integer_row_value {σ : Type*} [Fintype σ] (a : σ → ℤ) (x : σ → ℝ)
    (hx : ∀ j, ∃ z : ℤ, x j = z) : ∃ z : ℤ, integerRow a x = z := by
  classical
  choose z hz using hx
  refine ⟨∑ j, a j * z j, ?_⟩
  simp [integerRow, hz]

/-- A half-unit outward shift changes no integer solutions of a row. -/
theorem integer_half_shift (u b : ℤ) :
    (u : ℝ) ≤ (b : ℝ) + 1 / 2 ↔ u ≤ b := by
  constructor
  · intro h
    by_contra hn
    have hi : b + 1 ≤ u := by omega
    have hr : (b : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast hi
    linarith
  · intro h
    have hr : (u : ℝ) ≤ (b : ℝ) := by exact_mod_cast h
    linarith

/-- Equality of the original and shifted integer feasible sets. This uses
actual integer rows, and is not asserted for unrestricted continuous points. -/
theorem shifted_feasible_iff {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (x : σ → ℝ) :
    x ∈ linearIntegerSet (fun i => integerRow (A i))
      (fun i => (b i : ℝ) + 1 / 2) Set.univ ↔
    x ∈ linearIntegerSet (fun i => integerRow (A i))
      (fun i => (b i : ℝ)) Set.univ := by
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨?_, hx⟩
    intro i
    obtain ⟨z, hz⟩ := integer_row_value (A i) x (fun j => hx j (Set.mem_univ j))
    have hi := h i
    rw [hz] at hi ⊢
    change (z : ℝ) ≤ (b i : ℝ)
    exact_mod_cast (integer_half_shift z (b i)).mp hi
  · rintro ⟨h, hx⟩
    refine ⟨?_, hx⟩
    intro i
    linarith [h i]

/-- All original feasible points have shifted slack at least one half. -/
theorem shifted_slack_positive {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (x : σ → ℝ)
    (hx : ∀ i, integerRow (A i) x ≤ (b i : ℝ)) (i : κ) :
    (1 : ℝ) / 2 ≤ (b i : ℝ) + 1 / 2 - integerRow (A i) x := by
  linarith [hx i]

/-- Closed shifted-slack intervals yield integer progression samples in the
ORIGINAL polytope; the intermediate real segment need only be in the relaxation. -/
theorem shifted_slack_integral_progression {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (x y : σ → ℝ) (T : ℝ) (k : ℤ)
    (hT : 0 < T)
    (hx : x ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ)
    (hy : y ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ)
    (hk : (k : ℝ) ∈ Set.Icc (-T) T)
    (hslacks : ∀ i, ∃ lo hi : ℝ, hi - lo ≤ lo / T ∧
      (lo ≤ (b i : ℝ) + 1 / 2 - integerRow (A i) x ∧
        (b i : ℝ) + 1 / 2 - integerRow (A i) x ≤ hi) ∧
      (lo ≤ (b i : ℝ) + 1 / 2 - integerRow (A i) y ∧
        (b i : ℝ) + 1 / 2 - integerRow (A i) y ≤ hi)) :
    (fun j => x j + (k : ℝ) * (y j - x j)) ∈
      linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ := by
  apply (shifted_feasible_iff A b _).mp
  apply slack_integral_progression (fun i => integerRow (A i))
    (fun i => (b i : ℝ) + 1 / 2) Set.univ x y T k hT
    ((shifted_feasible_iff A b x).mpr hx) ((shifted_feasible_iff A b y).mpr hy) hk
  intro i
  exact Or.inr (hslacks i)

/-- The shifted closed-cell hypotheses are connected to the final polynomial
error estimate. Coverage, complete candidates, extrema and Markov remain inputs. -/
theorem shifted_slack_cover_guarantee {σ ι κ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℝ) (A : κ → σ → ℤ) (b : κ → ℤ)
    (C : ι → Set (σ → ℝ)) (Y : Finset (σ → ℝ))
    (x : σ → ℝ) (fmax eps : ℝ) (D : ℕ)
    (hD : 0 < D) (heps : 0 < eps) (hdeg : f.totalDegree ≤ D)
    (hx : x ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ)
    (hbounds : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ,
      MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧ MvPolynomial.eval z f ≤ fmax)
    (hcover : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ,
      ∃ c, z ∈ C c)
    (hfeasible : ∀ y ∈ Y, y ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i : ℝ)) Set.univ)
    (hcomplete : ∀ c, (∃ z ∈ linearIntegerSet (fun i => integerRow (A i))
      (fun i => (b i : ℝ)) Set.univ, z ∈ C c) → ∃ y ∈ Y, y ∈ C c)
    (hmarkov : SampledMarkov.MarkovBound D
      (max (D ^ 2) ⌈(D : ℝ) / Real.sqrt eps⌉₊))
    (hslacks : ∀ c, ∀ u ∈ C c, ∀ v ∈ C c, ∀ i, ∃ lo hi : ℝ,
      hi - lo ≤ lo / (max (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊ : ℝ) ∧
      (lo ≤ (b i : ℝ) + 1 / 2 - integerRow (A i) u ∧
        (b i : ℝ) + 1 / 2 - integerRow (A i) u ≤ hi) ∧
      (lo ≤ (b i : ℝ) + 1 / 2 - integerRow (A i) v ∧
        (b i : ℝ) + 1 / 2 - integerRow (A i) v ≤ hi)) :
    ∃ best ∈ Y, best ∈ linearIntegerSet (fun i => integerRow (A i))
      (fun i => (b i : ℝ)) Set.univ ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f - MvPolynomial.eval x f ∧
      MvPolynomial.eval best f - MvPolynomial.eval x f ≤
        eps * (fmax - MvPolynomial.eval x f) := by
  apply certified_cover_guarantee f _ C Y x fmax eps D hD heps hdeg
    hx hbounds hcover hfeasible hcomplete hmarkov
  intro c u hu v hv huc hvc k hk
  apply shifted_slack_integral_progression A b u v _ k _ hu hv hk
    (hslacks c u huc v hvc)
  have hp := (FPTASCalculations.ceiling_refinement hD heps).1
  have : (0 : ℝ) < (↑(max (D^2) ⌈(D : ℝ) / Real.sqrt eps⌉₊) : ℝ) := by
    exact_mod_cast hp
  simpa only [Nat.cast_max, Nat.cast_pow] using this

end LineRestriction

