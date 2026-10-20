import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Log

namespace ScaledPolynomial
open MvPolynomial
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Total exponent of the coordinates divided by Q. -/
def weight (I : Finset σ) (a : σ →₀ ℕ) : ℕ := ∑ i ∈ I, a i

/-- An integer polynomial, constructed before any division takes place. -/
noncomputable def scaled (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ) :
    MvPolynomial σ ℤ :=
  ∑ a ∈ f.support, monomial a (f.coeff a * Q ^ (D - weight I a))

theorem weight_le (I : Finset σ) (a : σ →₀ ℕ) :
    weight I a ≤ a.sum (fun _ e => e) := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ I)

theorem coefficient (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ)
    (a : σ →₀ ℕ) :
    (scaled f I Q D).coeff a = f.coeff a * Q ^ (D - weight I a) := by
  classical
  simp only [scaled, coeff_sum, coeff_monomial]
  by_cases ha : a ∈ f.support
  · simp [ha]
  · have hz : f.coeff a = 0 := notMem_support_iff.mp ha
    simp [ha, hz]

/-- For nonzero Q no monomials disappear, including the constant/zero cases. -/
theorem support_scaled (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ)
    (hQ : Q ≠ 0) : (scaled f I Q D).support = f.support := by
  ext a
  simp only [mem_support_iff, coefficient, mul_ne_zero]
  simp [pow_ne_zero _ hQ]

theorem degree_bound (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ) :
    (scaled f I Q D).totalDegree ≤ f.totalDegree := by
  apply totalDegree_finsetSum_le
  intro a ha
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree ha)

theorem degree_preserved (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ)
    (hQ : Q ≠ 0) : (scaled f I Q D).totalDegree = f.totalDegree := by
  simp only [totalDegree, support_scaled f I Q D hQ]

theorem monomial_substitution (I : Finset σ) (a : σ →₀ ℕ) (u : σ → ℝ)
    (Q : ℝ) (hQ : Q ≠ 0) :
    a.prod (fun i e => (if i ∈ I then u i / Q else u i)^e) =
      a.prod (fun i e => u i ^ e) / Q ^ weight I a := by
  classical
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  have he : ∀ i : σ, (if i ∈ I then u i / Q else u i) ^ a i =
      u i ^ a i / Q ^ (if i ∈ I then a i else 0) := by
    intro i
    split_ifs <;> simp [div_pow]
  simp_rw [he]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  simp [weight]

theorem eval_scaled (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ)
    (hQ : Q ≠ 0) (hD : f.totalDegree ≤ D) (u : σ → ℝ) :
    (scaled f I Q D).eval₂ (Int.castRingHom ℝ) u =
      (Q : ℝ)^D * f.eval₂ (Int.castRingHom ℝ)
        (fun i => if i ∈ I then u i / Q else u i) := by
  classical
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  rw [scaled, eval₂_sum, eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [eval₂_monomial]
  simp only [map_mul, map_pow]
  change ((f.coeff a : ℤ) : ℝ) * (Q : ℝ)^(D - weight I a) * a.prod (fun i e => u i^e) =
    (Q : ℝ)^D * (((f.coeff a : ℤ) : ℝ) *
      a.prod (fun i e => (if i ∈ I then u i / (Q : ℝ) else u i)^e))
  rw [monomial_substitution I a u Q hQr]
  have hw : weight I a ≤ D := (weight_le I a).trans ((le_totalDegree ha).trans hD)
  have hp : (Q : ℝ)^D = (Q : ℝ)^(D - weight I a) * (Q : ℝ)^weight I a := by
    rw [← pow_add, Nat.sub_add_cancel hw]
  rw [hp]
  field_simp

/-- The denominator-cleared polynomial exists over the integers, with exactly
the same support and degree, and represents the desired real-valued function. -/
theorem integer_representation (f : MvPolynomial σ ℤ) (I : Finset σ)
    (Q : ℤ) (D : ℕ) (hQ : Q ≠ 0) (hD : f.totalDegree ≤ D) :
    ∃ g : MvPolynomial σ ℤ, g.support = f.support ∧ g.totalDegree ≤ D ∧
      ∀ u : σ → ℝ, g.eval₂ (Int.castRingHom ℝ) u =
        (Q : ℝ)^D * f.eval₂ (Int.castRingHom ℝ)
          (fun i => if i ∈ I then u i / Q else u i) := by
  exact ⟨scaled f I Q D, support_scaled f I Q D hQ,
    (degree_bound f I Q D).trans hD, eval_scaled f I Q D hQ hD⟩

/-- Signed binary length, with one sign bit (including zero). -/
def bitSize (z : ℤ) : ℕ := 1 + z.natAbs.size

/-- The bit length agrees with the integer ceiling-log convention. -/
theorem bitSize_eq_clog (z : ℤ) : bitSize z = 1 + Nat.clog 2 (z.natAbs + 1) := by
  unfold bitSize
  congr 1
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.size_le, Nat.clog_le_iff_le_pow (by decide)]
  omega

theorem size_mul_le (a b : ℕ) : (a*b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (Nat.lt_size_self a) (Nat.lt_size_self b)

theorem size_mul_pow_le (a b e : ℕ) : (a*b^e).size ≤ a.size + e*b.size := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, ← mul_assoc]
    have hm := size_mul_le (a*b^e) b
    simp only [Nat.succ_mul]
    omega

theorem coefficient_bits (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ)
    (D : ℕ) (a : σ →₀ ℕ) :
    bitSize ((scaled f I Q D).coeff a) ≤ bitSize (f.coeff a) + D * Q.natAbs.size := by
  rw [coefficient]
  simp only [bitSize, Int.natAbs_mul, Int.natAbs_pow]
  have h := size_mul_pow_le (f.coeff a).natAbs Q.natAbs (D - weight I a)
  have hm := Nat.mul_le_mul_right Q.natAbs.size (Nat.sub_le D (weight I a))
  omega

/-- Total coefficient payload, before unchanged exponents/list metadata. -/
theorem coefficient_payload (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ)
    (D : ℕ) (hQ : Q ≠ 0) :
    (∑ a ∈ (scaled f I Q D).support, bitSize ((scaled f I Q D).coeff a)) ≤
      (∑ a ∈ f.support, bitSize (f.coeff a)) + f.support.card * (D * Q.natAbs.size) := by
  rw [support_scaled f I Q D hQ]
  calc
    _ ≤ ∑ a ∈ f.support, (bitSize (f.coeff a) + D * Q.natAbs.size) :=
      Finset.sum_le_sum (fun a _ => coefficient_bits f I Q D a)
    _ = _ := by simp [Finset.sum_add_distrib]

noncomputable def encode (I : Finset σ) (Q : ℤ) (x : σ → ℝ) : σ → ℝ :=
  fun i => if i ∈ I then (Q : ℝ)*x i else x i
noncomputable def decode (I : Finset σ) (Q : ℤ) (u : σ → ℝ) : σ → ℝ :=
  fun i => if i ∈ I then u i/(Q : ℝ) else u i

theorem decode_encode (I : Finset σ) (Q : ℤ) (hQ : Q ≠ 0) (x : σ → ℝ) :
    decode I Q (encode I Q x) = x := by
  have h : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  funext i
  by_cases hi : i ∈ I <;> simp [decode, encode, hi] <;> field_simp [h]

theorem encode_decode (I : Finset σ) (Q : ℤ) (hQ : Q ≠ 0) (u : σ → ℝ) :
    encode I Q (decode I Q u) = u := by
  have h : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  funext i
  by_cases hi : i ∈ I <;> simp [decode, encode, hi] <;> field_simp [h]

def scaledRow (a : σ → ℤ) (I : Finset σ) (Q : ℤ) : σ → ℤ :=
  fun i => if i ∈ I then a i else Q*a i

/-- Multiplication increases signed binary length by at most the multiplier's magnitude length. -/
theorem bitSize_mul (Q c : ℤ) :
    bitSize (Q*c) ≤ bitSize c + Q.natAbs.size := by
  simp only [bitSize, Int.natAbs_mul]
  have h := size_mul_le Q.natAbs c.natAbs
  omega

/-- Continuous columns are unchanged; every other column is multiplied by Q. -/
theorem scaledRow_bits (a : σ → ℤ) (I : Finset σ) (Q : ℤ) (i : σ) :
    bitSize (scaledRow a I Q i) ≤ bitSize (a i) + Q.natAbs.size := by
  by_cases hi : i ∈ I
  · simp [scaledRow, hi]
  · simpa [scaledRow, hi] using bitSize_mul Q (a i)

theorem scaled_rhs_bits (b Q : ℤ) :
    bitSize (Q*b) ≤ bitSize b + Q.natAbs.size := bitSize_mul Q b

/-- Dense row payload, including the right-hand side. -/
def rowPayload (a : σ → ℤ) (b : ℤ) : ℕ := (∑ i, bitSize (a i)) + bitSize b

theorem scaled_row_payload (a : σ → ℤ) (b : ℤ) (I : Finset σ) (Q : ℤ) :
    rowPayload (scaledRow a I Q) (Q*b) ≤
      rowPayload a b + (Fintype.card σ + 1)*Q.natAbs.size := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => scaledRow_bits a I Q i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have hb := scaled_rhs_bits b Q
  simp only [rowPayload, Nat.add_mul, Nat.one_mul]
  omega

/-- Full dense constraint payload; the number of rows and columns is unchanged. -/
theorem scaled_constraints_payload {κ : Type*} [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (I : Finset σ) (Q : ℤ) :
    (∑ j, rowPayload (scaledRow (A j) I Q) (Q*b j)) ≤
      (∑ j, rowPayload (A j) (b j)) +
        Fintype.card κ * ((Fintype.card σ + 1)*Q.natAbs.size) := by
  calc
    _ ≤ ∑ j, (rowPayload (A j) (b j) +
        (Fintype.card σ + 1)*Q.natAbs.size) :=
      Finset.sum_le_sum (fun j _ => scaled_row_payload (A j) (b j) I Q)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Any fixed dimension/list metadata may be included on both sides. -/
theorem scaled_constraints_encoding {κ : Type*} [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (I : Finset σ) (Q : ℤ) (metadata : ℕ) :
    metadata + (∑ j, rowPayload (scaledRow (A j) I Q) (Q*b j)) ≤
      metadata + (∑ j, rowPayload (A j) (b j)) +
        Fintype.card κ * ((Fintype.card σ + 1)*Q.natAbs.size) := by
  have h := scaled_constraints_payload A b I Q
  omega

theorem row_identity (a : σ → ℤ) (I : Finset σ) (Q : ℤ) (hQ : Q ≠ 0)
    (u : σ → ℝ) :
    (∑ i, (scaledRow a I Q i : ℝ)*u i) =
      (Q : ℝ) * ∑ i, (a i : ℝ)*decode I Q u i := by
  have h : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · simp [scaledRow, decode, hi]
    field_simp
  · simp [scaledRow, decode, hi]
    ring

def integral (u : σ → ℝ) : Prop := ∀ i, ∃ z : ℤ, u i = z

def gridFeasible {κ : Type*} (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) (Q : ℤ) (x : σ → ℝ) : Prop :=
  (∀ j, (∑ i, (A j i : ℝ)*x i) ≤ (b j : ℝ)) ∧ integral (encode I Q x)

def scaledFeasible {κ : Type*} (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) (Q : ℤ) (u : σ → ℝ) : Prop :=
  (∀ j, (∑ i, (scaledRow (A j) I Q i : ℝ)*u i) ≤ (Q*b j : ℤ)) ∧ integral u

/-- Grid membership means exactly x_i is in Q^{-1} Z on continuous
coordinates and in Z on the remaining coordinates. -/
theorem grid_coordinates (I : Finset σ) (Q : ℤ) (hQ : Q ≠ 0) (x : σ → ℝ) :
    integral (encode I Q x) ↔
      ∀ i, ∃ z : ℤ, x i = if i ∈ I then (z : ℝ)/Q else (z : ℝ) := by
  have h : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  constructor
  · intro hx i
    obtain ⟨z, hz⟩ := hx i
    refine ⟨z, ?_⟩
    by_cases hi : i ∈ I
    · simp [encode, hi] at hz ⊢
      apply (eq_div_iff h).mpr
      nlinarith
    · simpa [encode, hi] using hz
  · intro hx i
    obtain ⟨z, hz⟩ := hx i
    refine ⟨z, ?_⟩
    by_cases hi : i ∈ I <;> simp [encode, hi, hz] <;> field_simp [h]

/-- The actual scaled integer inequalities are equivalent to the grid system. -/
theorem scaled_feasible_iff {κ : Type*} (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) (Q : ℤ) (hQ : 0 < Q) (u : σ → ℝ) :
    scaledFeasible A b I Q u ↔ gridFeasible A b I Q (decode I Q u) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hn : Q ≠ 0 := ne_of_gt hQ
  simp only [scaledFeasible, gridFeasible, encode_decode I Q hn,
    row_identity _ I Q hn, Int.cast_mul, mul_le_mul_iff_right₀ hQr]

theorem grid_feasible_iff {κ : Type*} (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) (Q : ℤ) (hQ : 0 < Q) (x : σ → ℝ) :
    gridFeasible A b I Q x ↔ scaledFeasible A b I Q (encode I Q x) := by
  rw [scaled_feasible_iff A b I Q hQ, decode_encode I Q (ne_of_gt hQ)]

theorem feasible_bijection {κ : Type*} (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) (Q : ℤ) (hQ : 0 < Q) :
    Function.Bijective (fun u : {u // scaledFeasible A b I Q u} =>
      (⟨decode I Q u.val, (scaled_feasible_iff A b I Q hQ u.val).mp u.property⟩ :
        {x // gridFeasible A b I Q x})) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    have hv := congrArg (fun x : {x // gridFeasible A b I Q x} => encode I Q x.val) huv
    simpa only [encode_decode I Q (ne_of_gt hQ)] using hv
  · intro x
    refine ⟨⟨encode I Q x.val, (grid_feasible_iff A b I Q hQ x.val).mp x.property⟩, ?_⟩
    apply Subtype.ext
    exact decode_encode I Q (ne_of_gt hQ) x.val

/-- Product denominator for a finite list of rational entries (including a row's RHS). -/
def commonDen (v : σ → ℚ) : ℕ := ∏ i, (v i).den

def clearedEntry (v : σ → ℚ) (i : σ) : ℤ :=
  (v i).num * (commonDen v / (v i).den : ℕ)

theorem commonDen_pos (v : σ → ℚ) : 0 < commonDen v := by
  exact Finset.prod_pos (fun i _ => (v i).den_pos)

theorem denominator_dvd (v : σ → ℚ) (i : σ) : (v i).den ∣ commonDen v := by
  exact Finset.dvd_prod_of_mem (fun j => (v j).den) (Finset.mem_univ i)

/-- This is an actual integer entry, equal in R to the positively scaled rational entry. -/
theorem clearedEntry_real (v : σ → ℚ) (i : σ) :
    (clearedEntry v i : ℝ) = (commonDen v : ℝ) * (v i : ℝ) := by
  have hd : (v i).den ≠ 0 := (v i).den_ne_zero
  have hmul : commonDen v / (v i).den * (v i).den = commonDen v :=
    Nat.div_mul_cancel (denominator_dvd v i)
  have hr : ((commonDen v / (v i).den : ℕ) : ℝ) * ((v i).den : ℝ) = commonDen v := by
    exact_mod_cast hmul
  have hdR : ((v i).den : ℝ) ≠ 0 := by exact_mod_cast hd
  simp only [clearedEntry, Int.cast_mul, Int.cast_natCast, Rat.cast_def]
  field_simp
  nlinarith [congrArg (fun t : ℝ => ((v i).num : ℝ) * t) hr]

/-- The extra one handles the empty product. -/
theorem size_prod_le (s : Finset σ) (a : σ → ℕ) :
    (∏ i ∈ s, a i).size ≤ 1 + ∑ i ∈ s, (a i).size := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have h := size_mul_le (a i) (∏ j ∈ s, a j)
    omega

theorem commonDen_bits (v : σ → ℚ) :
    (commonDen v).size ≤ 1 + ∑ i, (v i).den.size := size_prod_le Finset.univ _

theorem clearedEntry_bits (v : σ → ℚ) (i : σ) :
    bitSize (clearedEntry v i) ≤ bitSize (v i).num + 1 + ∑ j, (v j).den.size := by
  have h := bitSize_mul (commonDen v / (v i).den : ℕ) (v i).num
  have hdiv : (commonDen v / (v i).den).size ≤ (commonDen v).size :=
    Nat.size_le_size (Nat.div_le_self _ _)
  have hp := commonDen_bits v
  simp only [Int.natAbs_natCast] at h
  unfold clearedEntry
  rw [mul_comm]
  omega

theorem cleared_payload (v : σ → ℚ) :
    (∑ i, bitSize (clearedEntry v i)) ≤
      (∑ i, bitSize (v i).num) + Fintype.card σ * (1 + ∑ i, (v i).den.size) := by
  calc
    _ ≤ ∑ i, (bitSize (v i).num + (1 + ∑ j, (v j).den.size)) :=
      Finset.sum_le_sum (fun i _ => by simpa [Nat.add_assoc] using clearedEntry_bits v i)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Append the RHS to each row before clearing denominators. -/
def rationalRow (a : σ → ℚ) (b : ℚ) : Option σ → ℚ :=
  fun i => match i with | none => b | some j => a j

/-- Clearing a rational inequality preserves its real solution set. -/
theorem cleared_row_iff (a : σ → ℚ) (b : ℚ) (x : σ → ℝ) :
    (∑ i, (clearedEntry (rationalRow a b) (some i) : ℝ)*x i) ≤
      (clearedEntry (rationalRow a b) none : ℝ) ↔
    (∑ i, (a i : ℝ)*x i) ≤ (b : ℝ) := by
  have hp : (0 : ℝ) < commonDen (rationalRow a b) := by
    exact_mod_cast commonDen_pos (rationalRow a b)
  simp_rw [clearedEntry_real]
  simp only [rationalRow]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_le_mul_iff_right₀ hp]

/-- Rows may have different positive product denominators. -/
theorem cleared_system_iff {κ : Type*} (A : κ → σ → ℚ) (b : κ → ℚ)
    (x : σ → ℝ) :
    (∀ j, (∑ i, (clearedEntry (rationalRow (A j) (b j)) (some i) : ℝ)*x i) ≤
      (clearedEntry (rationalRow (A j) (b j)) none : ℝ)) ↔
    (∀ j, (∑ i, (A j i : ℝ)*x i) ≤ (b j : ℝ)) := by
  exact forall_congr' (fun j => cleared_row_iff (A j) (b j) x)

/-- Any additional domain restriction, including integrality, is preserved. -/
theorem cleared_domain_iff {κ : Type*} (A : κ → σ → ℚ) (b : κ → ℚ)
    (domain : (σ → ℝ) → Prop) (x : σ → ℝ) :
    ((∀ j, (∑ i, (clearedEntry (rationalRow (A j) (b j)) (some i) : ℝ)*x i) ≤
      (clearedEntry (rationalRow (A j) (b j)) none : ℝ)) ∧ domain x) ↔
    ((∀ j, (∑ i, (A j i : ℝ)*x i) ≤ (b j : ℝ)) ∧ domain x) := by
  rw [cleared_system_iff]

/-- Rational payload uses signed numerator bits and positive denominator bits. -/
def rationalPayload (v : σ → ℚ) : ℕ :=
  (∑ i, bitSize (v i).num) + ∑ i, (v i).den.size

/-- A quadratic bound in the original rational payload, without a separate entry count. -/
theorem cleared_payload_quadratic (v : σ → ℚ) :
    (∑ i, bitSize (clearedEntry v i)) ≤ rationalPayload v * (rationalPayload v + 2) := by
  have h := cleared_payload v
  have hn : Fintype.card σ ≤ ∑ i, bitSize (v i).num := by
    calc
      _ = ∑ _i : σ, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => by simp [bitSize])
  have hnL : Fintype.card σ ≤ rationalPayload v := by unfold rationalPayload; omega
  have hs : (∑ i, bitSize (v i).num) ≤ rationalPayload v := by unfold rationalPayload; omega
  have hd : (∑ i, (v i).den.size) ≤ rationalPayload v := by unfold rationalPayload; omega
  have hm := Nat.mul_le_mul hnL (Nat.add_le_add_left hd 1)
  nlinarith

/-- Summing row bounds gives a polynomial bound for the whole normalized matrix and RHS. -/
theorem cleared_matrix_payload {κ : Type*} [Fintype κ]
    (A : κ → σ → ℚ) (b : κ → ℚ) :
    (∑ j, ∑ i, bitSize (clearedEntry (rationalRow (A j) (b j)) i)) ≤
      ∑ j, rationalPayload (rationalRow (A j) (b j)) *
        (rationalPayload (rationalRow (A j) (b j)) + 2) := by
  exact Finset.sum_le_sum (fun j _ => cleared_payload_quadratic _)

/-- Leibniz determinant bound for an actual real matrix. -/
theorem determinant_bound (B : Matrix σ σ ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hB : ∀ i j, |B i j| ≤ C) :
    |B.det| ≤ (Fintype.card σ).factorial * C ^ Fintype.card σ := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ p : Equiv.Perm σ, |(Equiv.Perm.sign p : ℝ) * ∏ i, B (p i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Equiv.Perm σ, C ^ Fintype.card σ := by
      apply Finset.sum_le_sum
      intro p _
      simp only [abs_mul, abs_unit_intCast, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ _i : σ, C := Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hB _ _)
        _ = _ := by simp
    _ = _ := by simp [Fintype.card_perm]

/-- The numerical exponent used in the manuscript, with natural ceiling logarithm. -/
def coordinateExponent (d τ : ℕ) := d * (τ + Nat.clog 2 (d+1)) + 2

def slackExponent (d τ : ℕ) := τ + coordinateExponent d τ + Nat.clog 2 (d+1) + 2

theorem factorial_power_bound (d τ : ℕ) :
    (d.factorial : ℝ) * (2 : ℝ)^(d*τ) < 2 ^ coordinateExponent d τ := by
  have hf : (d.factorial : ℝ) ≤ (d : ℝ)^d := by exact_mod_cast Nat.factorial_le_pow d
  have hd : (d : ℝ) ≤ (2 : ℝ)^(Nat.clog 2 (d+1)) := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (d+1)
    exact_mod_cast (show d ≤ 2 ^ Nat.clog 2 (d+1) by omega)
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ d) hd d
  have hm := mul_le_mul_of_nonneg_right (hf.trans hp) (by positivity : (0:ℝ) ≤ 2^(d*τ))
  have he : ((2:ℝ)^Nat.clog 2 (d+1))^d * 2^(d*τ) = 2^(d*(τ+Nat.clog 2 (d+1))) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [he] at hm
  unfold coordinateExponent
  rw [pow_add]
  have hpos : (0:ℝ) < 2^(d*(τ+Nat.clog 2 (d+1))) := by positivity
  norm_num
  nlinarith

/-- An integral nonzero determinant has magnitude at least one. -/
theorem integer_denominator_gap (z : ℤ) (hz : z ≠ 0) : (1:ℝ) ≤ |(z:ℝ)| := by
  have h : (1:ℤ) ≤ |z| := by have := abs_pos.mpr hz; omega
  exact_mod_cast h

/-- Cramer's determinant ratio has the claimed coordinate bound.
The geometric Cramer representation is supplied explicitly. -/
theorem cramer_coordinate_bound (N : Matrix σ σ ℝ) (den : ℤ) (x : ℝ) (τ : ℕ)
    (hden : den ≠ 0) (hx : x = N.det / (den:ℝ))
    (hN : ∀ i j, |N i j| ≤ (2:ℝ)^τ) :
    |x| < 2 ^ coordinateExponent (Fintype.card σ) τ := by
  have hgap := integer_denominator_gap den hden
  have hdet := determinant_bound N (2^τ) (by positivity) hN
  have hp := factorial_power_bound (Fintype.card σ) τ
  have he : ((2:ℝ)^τ)^(Fintype.card σ) = 2^(Fintype.card σ*τ) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [he] at hdet
  rw [hx, abs_div]
  exact (div_le_self (abs_nonneg _) hgap).trans_lt (hdet.trans_lt hp)

/-- Convex combinations preserve a uniform strict coordinate bound. -/
theorem convex_coordinate_bound {κ : Type*} [Fintype κ]
    (w : κ → ℝ) (v : κ → ℝ) (R : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hv : ∀ k, |v k| < R) :
    |∑ k, w k*v k| < R := by
  have hex : ∃ k, 0 < w k := by
    by_contra h
    push_neg at h
    have hz : ∀ k, w k = 0 := fun k => le_antisymm (h k) (hw k)
    simp [hz] at hs
  obtain ⟨k,hk⟩ := hex
  calc
    _ ≤ ∑ k, |w k*v k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, w k*|v k| := by simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ < ∑ k, w k*R := by
      apply Finset.sum_lt_sum
      · intro j _
        exact mul_le_mul_of_nonneg_left (hv j).le (hw j)
      · exact ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (hv k) hk⟩
    _ = R := by rw [← Finset.sum_mul, hs, one_mul]

/-- Bound a feasible row slack from coefficient and coordinate bounds. -/
theorem slack_magnitude_bound (a x : σ → ℝ) (b C R : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (ha : ∀ i, |a i| ≤ C)
    (hx : ∀ i, |x i| ≤ R) (hb : |b| ≤ C) (hfeas : ∑ i, a i*x i ≤ b) :
    0 ≤ b - ∑ i, a i*x i ∧ b - ∑ i, a i*x i ≤ C*(1 + Fintype.card σ*R) := by
  constructor
  · linarith
  · have hp : |∑ i, a i*x i| ≤ Fintype.card σ*(C*R) := by
      calc
        _ ≤ ∑ i, |a i*x i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : σ, C*R := Finset.sum_le_sum (fun i _ => by
          rw [abs_mul]; exact mul_le_mul (ha i) (hx i) (abs_nonneg _) hC)
        _ = _ := by simp
    have hb' := le_abs_self b
    have hs := neg_le_abs (∑ i, a i*x i)
    nlinarith

theorem slack_power_bound (d τ : ℕ) :
    (2:ℝ)^τ*(1 + d*2^coordinateExponent d τ) < 2^slackExponent d τ := by
  have hd : (d:ℝ) + 1 ≤ (2:ℝ)^Nat.clog 2 (d+1) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (d+1)
  have hv : (1:ℝ) ≤ 2^coordinateExponent d τ := one_le_pow₀ (by norm_num)
  have hV : (0:ℝ) < 2^coordinateExponent d τ := by positivity
  have hT : (0:ℝ) < 2^τ := by positivity
  have hL : (0:ℝ) < 2^Nat.clog 2 (d+1) := by positivity
  have h : 1+(d:ℝ)*2^coordinateExponent d τ ≤
      2^Nat.clog 2 (d+1)*2^coordinateExponent d τ := by nlinarith
  have hm := mul_le_mul_of_nonneg_left h hT.le
  unfold slackExponent
  simp only [pow_add]
  norm_num
  nlinarith

theorem dyadic_slack_bound (a x : σ → ℝ) (b : ℝ) (τ : ℕ)
    (ha : ∀ i, |a i| ≤ (2:ℝ)^τ) (hb : |b| ≤ (2:ℝ)^τ)
    (hx : ∀ i, |x i| < 2^coordinateExponent (Fintype.card σ) τ)
    (hfeas : ∑ i, a i*x i ≤ b) :
    0 ≤ b - ∑ i, a i*x i ∧ b - ∑ i, a i*x i < 2^slackExponent (Fintype.card σ) τ := by
  have h := slack_magnitude_bound a x b (2^τ) _ (by positivity) (by positivity) ha
    (fun i => (hx i).le) hb hfeas
  exact ⟨h.1, h.2.trans_lt (slack_power_bound _ τ)⟩

/-- Conditional polytope interface: Cramer data for the vertices plus a convex
representation of the point yield both coordinate and feasible-row slack bounds. -/
theorem represented_point_bounds {κ : Type*} [Fintype κ]
    (v : κ → σ → ℝ) (w : κ → ℝ) (x a : σ → ℝ) (b : ℝ) (τ : ℕ)
    (N : κ → σ → Matrix σ σ ℝ) (den : κ → σ → ℤ)
    (hden : ∀ k i, den k i ≠ 0)
    (hcramer : ∀ k i, v k i = (N k i).det / (den k i : ℝ))
    (hN : ∀ k i r c, |N k i r c| ≤ (2:ℝ)^τ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hx : ∀ i, x i = ∑ k, w k*v k i)
    (ha : ∀ i, |a i| ≤ (2:ℝ)^τ) (hb : |b| ≤ (2:ℝ)^τ)
    (hfeas : ∑ i, a i*x i ≤ b) :
    (∀ i, |x i| < 2^coordinateExponent (Fintype.card σ) τ) ∧
    (0 ≤ b - ∑ i, a i*x i ∧ b - ∑ i, a i*x i < 2^slackExponent (Fintype.card σ) τ) := by
  have hc : ∀ i, |x i| < 2^coordinateExponent (Fintype.card σ) τ := by
    intro i
    rw [hx i]
    apply convex_coordinate_bound w (fun k => v k i) _ hw hs
    intro k
    exact cramer_coordinate_bound (N k i) (den k i) (v k i) τ (hden k i) (hcramer k i) (hN k i)
  exact ⟨hc, dyadic_slack_bound a x b τ ha hb hc hfeas⟩

/-- Single coordinate-and-slack exponent Phi used in the manuscript. -/
def unifiedExponent (d τ : ℕ) := (d+1)*(τ+Nat.clog 2 (d+1))+4

theorem unified_exponent_eq (d τ : ℕ) : unifiedExponent d τ = slackExponent d τ := by
  unfold unifiedExponent slackExponent coordinateExponent
  ring

theorem unified_point_bounds {κ : Type*} [Fintype κ]
    (v : κ → σ → ℝ) (w : κ → ℝ) (x a : σ → ℝ) (b : ℝ) (τ : ℕ)
    (N : κ → σ → Matrix σ σ ℝ) (den : κ → σ → ℤ)
    (hden : ∀ k i, den k i ≠ 0)
    (hcramer : ∀ k i, v k i = (N k i).det / (den k i : ℝ))
    (hN : ∀ k i r c, |N k i r c| ≤ (2:ℝ)^τ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1)
    (hx : ∀ i, x i = ∑ k, w k*v k i)
    (ha : ∀ i, |a i| ≤ (2:ℝ)^τ) (hb : |b| ≤ (2:ℝ)^τ)
    (hfeas : ∑ i, a i*x i ≤ b) :
    (∀ i, |x i| < 2^unifiedExponent (Fintype.card σ) τ) ∧
    (0 ≤ b - ∑ i, a i*x i ∧ b - ∑ i, a i*x i < 2^unifiedExponent (Fintype.card σ) τ) := by
  have h := represented_point_bounds v w x a b τ N den hden hcramer hN hw hs hx ha hb hfeas
  have he : coordinateExponent (Fintype.card σ) τ ≤ unifiedExponent (Fintype.card σ) τ := by
    rw [unified_exponent_eq]
    unfold slackExponent
    omega
  constructor
  · intro i
    exact (h.1 i).trans_le (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he)
  · simpa only [unified_exponent_eq] using h.2

/-- Candidate continuous bases are r-subsets of the m constraint rows. -/
theorem continuous_basis_count (m r : ℕ) :
    ((Finset.univ : Finset (Fin m)).powersetCard r).card = m.choose r := by simp

/-- Polynomial bound on the number of candidate bases. -/
theorem continuous_basis_power_bound (m r phi : ℕ) (hm : m ≤ phi) :
    m.choose r ≤ phi^r := (Nat.choose_le_pow m r).trans (Nat.pow_le_pow_left hm r)

/-- The actual lcm is positive and a multiple of every nonzero determinant. -/
theorem basis_lcm_spec (s : Finset σ) (v : σ → ℕ)
    (hv : ∀ i ∈ s, v i ≠ 0) :
    0 < s.lcm v ∧ ∀ i ∈ s, v i ∣ s.lcm v := by
  exact ⟨Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.2 hv), fun _ hi => Finset.dvd_lcm hi⟩

/-- Encoding length of the actual lcm, including the empty family. -/
theorem basis_lcm_size (s : Finset σ) (v : σ → ℕ) (N E : ℕ)
    (hv : ∀ i ∈ s, v i ≠ 0) (hcard : s.card ≤ N)
    (hbits : ∀ i ∈ s, (v i).size ≤ E) :
    (s.lcm v).size ≤ 1+N*E := by
  have hp : 0 < ∏ i ∈ s, v i := Finset.prod_pos (fun i hi => Nat.pos_of_ne_zero (hv i hi))
  have hl := Nat.le_of_dvd hp (Finset.lcm_dvd_prod s v)
  have hb := (Nat.size_le_size hl).trans (size_prod_le s v)
  have hsum : (∑ i ∈ s, (v i).size) ≤ s.card*E := by
    calc
      _ ≤ ∑ _i ∈ s, E := Finset.sum_le_sum hbits
      _ = _ := by simp
  have hc := Nat.mul_le_mul_right E hcard
  omega

/-- Bits of Q=k*Delta, with the determinant-lcm estimate substituted. -/
theorem mixed_grid_size (s : Finset σ) (v : σ → ℕ) (N E k : ℕ)
    (hv : ∀ i ∈ s, v i ≠ 0) (hcard : s.card ≤ N)
    (hbits : ∀ i ∈ s, (v i).size ≤ E) :
    (k*s.lcm v).size ≤ k.size+1+N*E := by
  have h := size_mul_le k (s.lcm v)
  have hl := basis_lcm_size s v N E hv hcard hbits
  omega

/-- Absorb basis count, determinant bits and grid multiplier bits into a power. -/
theorem mixed_grid_polynomial_size (phi r c N E K Qbits : ℕ)
    (hphi : 2 ≤ phi) (hN : N ≤ phi^r) (hE : E ≤ phi^c)
    (hK : K ≤ phi^c) (hQ : Qbits ≤ K+1+N*E) :
    Qbits ≤ phi^(r+c+2) := by
  have hp : 1 ≤ phi := by omega
  have hpow : 1 ≤ phi^(r+c) := Nat.one_le_pow _ _ hp
  have hcp : phi^c ≤ phi^(r+c) := Nat.pow_le_pow_right hp (by omega)
  have hne : N*E ≤ phi^(r+c) := by
    calc
      _ ≤ phi^r*phi^c := Nat.mul_le_mul hN hE
      _ = _ := (pow_add _ _ _).symm
  have hphi2 : 3 ≤ phi^2 := by nlinarith
  calc
    Qbits ≤ 3*phi^(r+c) := by omega
    _ ≤ phi^(r+c)*phi^2 := by nlinarith
    _ = _ := (pow_add _ _ _).symm

/-- Aggregate scaled input size from the established payload-increase bound. -/
theorem mixed_scaled_input_size (phi r a b W Qbits S : ℕ)
    (hphi : 2 ≤ phi) (ha : 1 ≤ a) (hW : W ≤ phi^b)
    (hQ : Qbits ≤ phi^(a*(r+1))) (hS : S ≤ phi+W*Qbits) :
    S ≤ phi^((a+b+1)*(r+1)) := by
  have hp : 1 ≤ phi := by omega
  have he : 1 ≤ b+a*(r+1) := by nlinarith
  have hbase : phi ≤ phi^(b+a*(r+1)) := by
    simpa using Nat.pow_le_pow_right hp he
  have hmul : W*Qbits ≤ phi^(b+a*(r+1)) := by
    calc
      _ ≤ phi^b*phi^(a*(r+1)) := Nat.mul_le_mul hW hQ
      _ = _ := (pow_add _ _ _).symm
  calc
    S ≤ 2*phi^(b+a*(r+1)) := by omega
    _ ≤ phi^(b+a*(r+1))*phi := by nlinarith
    _ = phi^(b+a*(r+1)+1) := (pow_succ _ _).symm
    _ ≤ phi^((a+b+1)*(r+1)) := Nat.pow_le_pow_right hp (by nlinarith)

/-- Compose preprocessing and the fixed-dimensional integer solver cost. -/
theorem mixed_runtime_composition (X S F prep run a r c d : ℕ)
    (hX : 2 ≤ X) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (hS : S ≤ X^(a*(r+1))) (hF : F ≤ X)
    (hprep : prep ≤ X^(a*(r+1))) (hrun : run ≤ (S*F)^(c*d)) :
    prep+run ≤ X^((a*(r+1)+1)*(c*d)+1) := by
  have hx : 1 ≤ X := by omega
  have hcd : 1 ≤ c*d := by nlinarith
  have hm : S*F ≤ X^(a*(r+1)+1) := by
    calc
      _ ≤ X^(a*(r+1))*X := Nat.mul_le_mul hS hF
      _ = _ := (pow_succ _ _).symm
  have hr : run ≤ X^((a*(r+1)+1)*(c*d)) := by
    calc
      _ ≤ (X^(a*(r+1)+1))^(c*d) := hrun.trans (Nat.pow_le_pow_left hm (c*d))
      _ = _ := (pow_mul _ _ _).symm
  have hp : prep ≤ X^((a*(r+1)+1)*(c*d)) := hprep.trans
    (Nat.pow_le_pow_right hx (by
      have hh := Nat.mul_le_mul_left (a*(r+1)+1) hcd
      omega))
  calc
    prep+run ≤ 2*X^((a*(r+1)+1)*(c*d)) := by omega
    _ ≤ X^((a*(r+1)+1)*(c*d))*X := by nlinarith
    _ = _ := (pow_succ _ _).symm

/-- Explicit absolute constant in the O(d(r+1)) exponent. -/
theorem mixed_runtime_exponent (a r c d : ℕ) (hd : 1 ≤ d) :
    (a*(r+1)+1)*(c*d)+1 ≤ ((a+1)*c+1)*d*(r+1) := by
  have h : 1 ≤ d*(r+1) := by nlinarith
  nlinarith [Nat.zero_le (c*d*r)]

/-- Integer determinant encoding bound from the already checked Leibniz estimate. -/
theorem integer_basis_determinant_size (B : Matrix σ σ ℝ) (z : ℤ) (tau : ℕ)
    (hz : B.det = (z : ℝ)) (hB : ∀ i j, |B i j| ≤ (2 : ℝ)^tau) :
    z.natAbs.size ≤ coordinateExponent (Fintype.card σ) tau := by
  have h := determinant_bound B ((2 : ℝ)^tau) (by positivity) hB
  have he : ((2 : ℝ)^tau)^(Fintype.card σ) = 2^(Fintype.card σ*tau) := by
    rw [← pow_mul, Nat.mul_comm]
  rw [he] at h
  have hlt := h.trans_lt (factorial_power_bound (Fintype.card σ) tau)
  rw [hz] at hlt
  have hnat : (z.natAbs : ℝ) < (2 : ℝ)^coordinateExponent (Fintype.card σ) tau := by
    simpa using hlt
  apply Nat.size_le.2
  exact_mod_cast hnat

/-- Integer slack intervals are exactly equivalent to rounding their endpoints. -/
theorem integer_slack_interval (s : ℤ) (lo hi : ℝ) :
    (lo ≤ (s : ℝ) ∧ (s : ℝ) ≤ hi) ↔ (⌈lo⌉ ≤ s ∧ s ≤ ⌊hi⌋) := by
  rw [Int.ceil_le, Int.le_floor]

/-- The half-unit shifted chamber endpoints round to bounds on integer slacks. -/
theorem shifted_integer_slack_interval (s : ℤ) (lo hi : ℝ) :
    (lo ≤ (s : ℝ)+1/2 ∧ (s : ℝ)+1/2 ≤ hi) ↔
      (⌈lo-1/2⌉ ≤ s ∧ s ≤ ⌊hi-1/2⌋) := by
  rw [← integer_slack_interval]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- For epsilon=a/b, its positive numerator cannot increase the grid multiplier. -/
theorem rational_grid_multiplier_le (D r a b k : ℕ) (ha : 1 ≤ a) (hb : 0 < b)
    (hk : (k : ℤ) = ⌈4*(D : ℝ)^2*r*(r+1)/((a : ℝ)/b)⌉) :
    k ≤ 4*D^2*r*(r+1)*b := by
  have hap : (0 : ℝ) < a := by exact_mod_cast ha
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hratio : 4*(D : ℝ)^2*r*(r+1)/((a : ℝ)/b) ≤
      (4*D^2*r*(r+1)*b : ℕ) := by
    push_cast
    rw [div_div_eq_mul_div]
    apply (div_le_iff₀ hap).2
    have har : (1 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 4*(D : ℝ)^2*r*(r+1)*b by positivity)
      (sub_nonneg.mpr har)]
  have h := (Int.ceil_le).2 hratio
  rw [← hk] at h
  exact_mod_cast h

/-- Explicit binary length of the actual ceiling multiplier; no real logarithms. -/
theorem rational_grid_multiplier_size (D r a b k : ℕ) (ha : 1 ≤ a) (hb : 0 < b)
    (hk : (k : ℤ) = ⌈4*(D : ℝ)^2*r*(r+1)/((a : ℝ)/b)⌉) :
    k.size ≤ 3+2*D.size+r.size+(r+1).size+b.size := by
  have h := Nat.size_le_size (rational_grid_multiplier_le D r a b k ha hb hk)
  have h1 := size_mul_pow_le 4 D 2
  have h2 := size_mul_le (4*D^2) r
  have h3 := size_mul_le (4*D^2*r) (r+1)
  have h4 := size_mul_le (4*D^2*r*(r+1)) b
  have hs4 : Nat.size 4 = 3 := by decide
  rw [hs4] at h1
  omega

/-- Combined constraint and polynomial payload, plus the denominator of epsilon/2.
Metadata includes unchanged exponent vectors, dimensions and list delimiters.
The accuracy numerator is unchanged; reduction of the fraction is unnecessary. -/
theorem full_scaled_input_payload {κ : Type*} [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (f : MvPolynomial σ ℤ)
    (I : Finset σ) (Q : ℤ) (D metadata accuracyDen : ℕ) (hQ : Q ≠ 0) :
    metadata + (∑ j, rowPayload (scaledRow (A j) I Q) (Q*b j)) +
      (∑ a ∈ (scaled f I Q D).support, bitSize ((scaled f I Q D).coeff a)) +
      (2*accuracyDen).size ≤
    metadata + (∑ j, rowPayload (A j) (b j)) +
      (∑ a ∈ f.support, bitSize (f.coeff a)) + accuracyDen.size +
      (Fintype.card κ*(Fintype.card σ+1)+f.support.card*D)*Q.natAbs.size + 2 := by
  have hc := scaled_constraints_payload A b I Q
  have hf := coefficient_payload f I Q D hQ
  have he := size_mul_le 2 accuracyDen
  have hs2 : Nat.size 2 = 2 := by decide
  rw [hs2] at he
  have hid : Fintype.card κ*((Fintype.card σ+1)*Q.natAbs.size) +
      f.support.card*(D*Q.natAbs.size) =
      (Fintype.card κ*(Fintype.card σ+1)+f.support.card*D)*Q.natAbs.size := by ring
  omega

end ScaledPolynomial
