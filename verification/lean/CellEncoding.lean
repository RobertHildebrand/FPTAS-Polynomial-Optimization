import CoverAssembly
import Mathlib.Data.Rat.Lemmas

namespace CellEncoding
open ScaledPolynomial CoverArithmetic CoverAssembly

/-- Reduction to lowest terms cannot enlarge either component. -/
theorem reduced_components (n : ℤ) (q : ℕ) (hq : 0 < q) :
    ((n : ℚ) / q).num.natAbs ≤ n.natAbs ∧ ((n : ℚ) / q).den ≤ q := by
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n
    (show (q : ℤ) ≠ 0 by omega)
  simp only [Int.cast_natCast] at hn hd
  have hc : c ≠ 0 := by intro h; simp [h] at hd; omega
  have hc' : 1 ≤ c.natAbs := by omega
  constructor
  · have h := congrArg Int.natAbs hn
    simp only [Int.natAbs_mul] at h
    rw [h]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · have h := congrArg Int.natAbs hd
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at h
    nlinarith

def ratBits (r : ℚ) := bitSize r.num + (1 + r.den.size)

theorem reduced_bits (n : ℤ) (q : ℕ) (hq : 0 < q) :
    ratBits ((n : ℚ) / q) ≤ bitSize n + q.size + 1 := by
  obtain ⟨hn, hd⟩ := reduced_components n q hq
  have := Nat.size_le_size hn
  have := Nat.size_le_size hd
  unfold ratBits bitSize
  omega

theorem threshold_fraction (ell k j : ℕ) (hell : 0 < ell) :
    threshold ell k j = ((2^k*(ell+j) : ℕ) : ℝ)/(4*ell) := by
  unfold threshold
  push_cast
  field_simp

/-- Every actual threshold has the same positive denominator and a bounded numerator. -/
theorem endpoint_fraction (Phi ell : ℕ) (hell : 0 < ell) (t : Endpoint Phi ell) :
    ∃ n : ℕ, n ≤ 4*ell*2^Phi ∧
      endpointRat t = (n : ℚ)/(4*ell) := by
  have ht := t.property
  simp only [thresholds, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range] at ht
  rcases ht with ht | ⟨⟨k,j⟩, ⟨hk,hj⟩, ht⟩
  · refine ⟨4*ell*2^Phi, le_rfl, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    rw [endpointRat_cast, ht]
    push_cast
    field_simp
  · have hk' : k ≤ Phi+1 := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk'
    refine ⟨2^k*(ell+j), ?_, ?_⟩
    · rw [pow_succ] at hp
      have hm := Nat.mul_le_mul hp (show ell+j ≤ 2*ell by omega)
      nlinarith
    · apply Rat.cast_injective (α := ℝ)
      rw [endpointRat_cast, ← ht, threshold_fraction ell k j hell]
      push_cast
      rfl

theorem endpoint_bits (Phi ell : ℕ) (hell : 0 < ell) (t : Endpoint Phi ell) :
    ratBits (endpointRat t) ≤ Phi + 2*ell.size + 8 := by
  obtain ⟨n,hn,he⟩ := endpoint_fraction Phi ell hell t
  have hq : 0 < 4*ell := by omega
  have hred := reduced_bits (n:ℤ) (4*ell) hq
  have hnsize := Nat.size_le_size hn
  have hmul := size_mul_le 4 ell
  have hnum := size_mul_pow_le (4*ell) 2 Phi
  have hpower : (4*ell*2^Phi).size ≤ (4*ell).size + Phi := by
    apply Nat.size_le.mpr
    have h := Nat.lt_size_self (4*ell)
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right h (by positivity)
  rw [he]
  simp only [bitSize, Int.natAbs_natCast, Int.cast_natCast, Nat.cast_mul, Nat.cast_ofNat] at hred
  have hfour : (4:ℕ).size = 3 := by decide
  rw [hfour] at hmul
  omega

/-- Generic signed sum bound, also used for rounded right-hand sides. -/
theorem signed_add_bits (a b : ℤ) :
    bitSize (a+b) ≤ bitSize a + bitSize b := by
  have ha := Nat.lt_size_self a.natAbs
  have hb := Nat.lt_size_self b.natAbs
  have hab := Int.natAbs_add_le a b
  unfold bitSize
  have hs : (a+b).natAbs.size ≤ a.natAbs.size+b.natAbs.size+1 := by
    apply Nat.size_le.mpr
    have hpa : 2^a.natAbs.size ≤ 2^(a.natAbs.size+b.natAbs.size) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpb : 2^b.natAbs.size ≤ 2^(a.natAbs.size+b.natAbs.size) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [pow_succ]
    omega
  omega

theorem signed_neg_bits (a : ℤ) : bitSize (-a) = bitSize a := by
  simp [bitSize]

theorem lower_endpoint {κ : Type*} {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) :
    ∃ t : Endpoint Phi ell, lowerSlack sign i = endpointRat t := by
  classical
  have h := Finset.max'_mem (lowerSlacks sign i) (lowerSlacks_nonempty sign i)
  simp only [lowerSlacks, Finset.mem_insert, Finset.mem_image] at h
  rcases h with h | ⟨t,_,ht⟩
  · have hm : (1/4:ℝ) ∈ thresholds Phi ell := by
      simpa [threshold] using threshold_mem Phi ell 0 0 (by omega) hell
    refine ⟨⟨1/4,hm⟩, ?_⟩
    change lowerSlack sign i = _ at h
    apply Rat.cast_injective (α := ℝ)
    rw [h,endpointRat_cast]
    norm_num
  · exact ⟨t,ht.symm⟩

theorem upper_endpoint {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) :
    ∃ t : Endpoint Phi ell, upperSlack sign i = endpointRat t := by
  classical
  have h := Finset.min'_mem (upperSlacks sign i) (upperSlacks_nonempty sign i)
  simp only [upperSlacks, Finset.mem_insert, Finset.mem_image] at h
  rcases h with h | ⟨t,_,ht⟩
  · have hm : (2:ℝ)^Phi ∈ thresholds Phi ell := Finset.mem_insert_self _ _
    refine ⟨⟨2^Phi,hm⟩, ?_⟩
    change upperSlack sign i = _ at h
    apply Rat.cast_injective (α := ℝ)
    rw [h,endpointRat_cast]
    norm_num
  · exact ⟨t,ht.symm⟩

theorem compressed_endpoint_bits {κ : Type*} {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) :
    ratBits (lowerSlack sign i) ≤ Phi+2*ell.size+8 ∧
    ratBits (upperSlack sign i) ≤ Phi+2*ell.size+8 := by
  obtain ⟨a,ha⟩ := lower_endpoint hell sign i
  obtain ⟨c,hc⟩ := upper_endpoint sign i
  rw [ha,hc]
  exact ⟨endpoint_bits Phi ell hell a, endpoint_bits Phi ell hell c⟩

theorem endpoint_range (Phi ell : ℕ) (hell : 0<ell) (t : Endpoint Phi ell) :
    0 ≤ (endpointRat t:ℝ) ∧ (endpointRat t:ℝ) ≤ (2:ℝ)^Phi := by
  obtain ⟨n,hn,he⟩ := endpoint_fraction Phi ell hell t
  rw [he]
  push_cast
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<4*ell)).mpr
    exact_mod_cast (show n ≤ 2^Phi*(4*ell) by nlinarith)

/-- Ceiling and floor after the half-shift have lengths independent of ell. -/
theorem rounded_bits (Phi : ℕ) (t : ℝ) (ht : 0≤t) (hu : t≤(2:ℝ)^Phi) :
    bitSize ⌈t-1/2⌉ ≤ Phi+2 ∧ bitSize ⌊t-1/2⌋ ≤ Phi+2 := by
  have hc0 : (0:ℤ) ≤ ⌈t-1/2⌉ := by
    exact Int.ceil_nonneg_of_neg_one_lt (by linarith)
  have hc1 : ⌈t-1/2⌉ ≤ (2:ℤ)^Phi := by
    apply Int.ceil_le.mpr
    push_cast
    linarith
  have hf0 : (-1:ℤ) ≤ ⌊t-1/2⌋ := by
    apply Int.le_floor.mpr
    norm_num
    linarith
  have hf1 : ⌊t-1/2⌋ ≤ (2:ℤ)^Phi := by
    apply Int.floor_le_iff.mpr
    push_cast
    linarith
  have hp : (1:ℤ) ≤ 2^Phi := one_le_pow₀ (by norm_num)
  have bound : ∀ z:ℤ, -((2:ℤ)^Phi) ≤ z → z ≤ (2:ℤ)^Phi → bitSize z ≤ Phi+2 := by
    intro z hz0 hz1
    have ha : z.natAbs ≤ (2:ℕ)^Phi := by
      have h : |z| ≤ ((2^Phi:ℕ):ℤ) := by simpa using abs_le.mpr ⟨hz0,hz1⟩
      have h' : (z.natAbs:ℤ) ≤ ((2^Phi:ℕ):ℤ) := by simpa using h
      exact_mod_cast h'
    have hs : z.natAbs.size ≤ Phi+1 := by
      apply Nat.size_le.mpr
      have hp' : 0 < (2:ℕ)^Phi := by positivity
      rw [pow_succ]
      omega
    unfold bitSize
    omega
  exact ⟨bound _ (by omega) hc1, bound _ (by omega) hf1⟩

theorem rat_neg_bits (r : ℚ) : ratBits (-r) = ratBits r := by
  simp [ratBits, bitSize]

/-- Rational LP right-hand side, including the original b entry. -/
theorem shifted_endpoint_bits (Phi ell : ℕ) (hell : 0<ell)
    (t : Endpoint Phi ell) (b : ℤ) :
    ratBits ((b:ℚ)+1/2-endpointRat t) ≤ bitSize b+Phi+4*ell.size+15 := by
  obtain ⟨n,hn,he⟩ := endpoint_fraction Phi ell hell t
  have hf : (b:ℚ)+1/2-endpointRat t =
      ((b*(4*ell)+2*ell-(n:ℤ):ℤ):ℚ)/(4*ell) := by
    rw [he]
    push_cast
    field_simp
    ring
  have hr := reduced_bits (b*(4*ell)+2*ell-(n:ℤ)) (4*ell) (by omega)
  have h1 := signed_add_bits (b*(4*ell)) (2*ell)
  have h2 := signed_add_bits (b*(4*ell)+2*ell) (-(n:ℤ))
  have h3 := bitSize_mul (4*ell:ℤ) b
  have h4 := size_mul_le 4 ell
  have h5 := size_mul_le 2 ell
  have hnsize := Nat.size_le_size hn
  have hpow : (4*ell*2^Phi).size ≤ (4*ell).size+Phi := by
    apply Nat.size_le.mpr
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (by positivity)
  have hf4 : (4:ℕ).size=3 := by decide
  have hf2 : (2:ℕ).size=2 := by decide
  rw [hf4] at h4
  rw [hf2] at h5
  rw [hf]
  simp only [bitSize, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.cast_mul, Nat.cast_ofNat] at hr h1 h2 h3 ⊢
  norm_num [Int.natAbs_neg, sub_eq_add_neg] at hr h1 h2 h3 ⊢
  simp only [mul_comm b.natAbs] at h1
  omega

theorem compressed_rhs_bits {κ : Type*} {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (b : κ → ℤ) (p : κ × Bool) :
    ratBits (compressedRhs b sign p) ≤ bitSize (b p.1)+Phi+4*ell.size+15 := by
  obtain ⟨a,ha⟩ := lower_endpoint hell sign p.1
  obtain ⟨c,hc⟩ := upper_endpoint sign p.1
  unfold compressedRhs
  split
  · rw [hc]
    have he : endpointRat c-(b p.1:ℚ)-1/2 = -((b p.1:ℚ)+1/2-endpointRat c) := by ring
    rw [he,rat_neg_bits]
    exact shifted_endpoint_bits Phi ell hell c _
  · rw [ha]
    exact shifted_endpoint_bits Phi ell hell a _

noncomputable def roundedRhs {κ : Type*} (b : κ → ℤ) {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (p : κ × Bool) : ℤ :=
  if p.2 then ⌊(upperSlack sign p.1:ℝ)-1/2⌋-b p.1
  else b p.1-⌈(lowerSlack sign p.1:ℝ)-1/2⌉

theorem rounded_rhs_bits {κ : Type*} {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (b : κ → ℤ) (p : κ × Bool) :
    bitSize (roundedRhs b sign p) ≤ bitSize (b p.1)+Phi+2 := by
  obtain ⟨a,ha⟩ := lower_endpoint hell sign p.1
  obtain ⟨c,hc⟩ := upper_endpoint sign p.1
  have har := endpoint_range Phi ell hell a
  have hcr := endpoint_range Phi ell hell c
  have hab := (rounded_bits Phi _ har.1 har.2).1
  have hcb := (rounded_bits Phi _ hcr.1 hcr.2).2
  unfold roundedRhs
  rw [ha,hc]
  split
  · have h := signed_add_bits ⌊(endpointRat c:ℝ)-1/2⌋ (-(b p.1))
    rw [signed_neg_bits] at h
    simpa only [sub_eq_add_neg] using h.trans (by omega)
  · have h := signed_add_bits (b p.1) (-⌈(endpointRat a:ℝ)-1/2⌉)
    rw [signed_neg_bits] at h
    simpa only [sub_eq_add_neg] using h.trans (by omega)

def roundedMatrix {σ κ : Type*} (A : κ → σ → ℤ) (p : κ × Bool) (j : σ) : ℤ :=
  if p.2 then -A p.1 j else A p.1 j

theorem rounded_matrix_bits {σ κ : Type*} (A : κ → σ → ℤ) (p : κ × Bool) (j : σ) :
    bitSize (roundedMatrix A p j) = bitSize (A p.1 j) := by
  unfold roundedMatrix
  split <;> simp [signed_neg_bits]

theorem rounded_system {σ κ : Type*} [Fintype σ] (A : κ → σ → ℤ) (b : κ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) (z : σ → ℤ) :
    (∀ p, ∑ j, roundedMatrix A p j*z j ≤ roundedRhs b sign p) ↔
    (∀ i, ⌈(lowerSlack sign i:ℝ)-1/2⌉ ≤ b i-∑ j,A i j*z j ∧
      b i-∑ j,A i j*z j ≤ ⌊(upperSlack sign i:ℝ)-1/2⌋) := by
  constructor
  · intro h i
    have hlo := h (i,false)
    have hhi := h (i,true)
    simp [roundedMatrix,roundedRhs,Finset.sum_neg_distrib] at hlo hhi
    simp only [one_div] at ⊢
    constructor <;> linarith
  · intro h p
    obtain ⟨i,u⟩ := p
    have hi := h i
    simp only [one_div] at hi
    cases u <;> simp [roundedMatrix,roundedRhs,Finset.sum_neg_distrib] <;> linarith

/-- Dense integer payload, including both RHS entries for each original row. -/
theorem rounded_cell_payload {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (tau : ℕ)
    (hA : ∀ i j,bitSize (A i j) ≤ tau) (hb : ∀ i,bitSize (b i) ≤ tau) :
    (∑ p : κ × Bool, ((∑ j,bitSize (roundedMatrix A p j))+bitSize (roundedRhs b sign p))) ≤
      2*Fintype.card κ*(Fintype.card σ*tau+tau+Phi+2) := by
  classical
  calc
    _ ≤ ∑ _p : κ × Bool, (Fintype.card σ*tau+tau+Phi+2) := by
      apply Finset.sum_le_sum
      intro p _
      have hm : (∑ j,bitSize (roundedMatrix A p j)) ≤ Fintype.card σ*tau := by
        calc
          _ ≤ ∑ _j : σ, tau := Finset.sum_le_sum (fun j _ => by rw [rounded_matrix_bits]; exact hA _ _)
          _ = _ := by simp
      have hr := rounded_rhs_bits hell sign b p
      have := hb p.1
      omega
    _ = _ := by simp [Fintype.card_prod]; ring

/-- Adding unchanged serialization metadata preserves the payload estimate. -/
theorem rounded_cell_encoding {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (tau metadata : ℕ)
    (hA : ∀ i j,bitSize (A i j) ≤ tau) (hb : ∀ i,bitSize (b i) ≤ tau) :
    (∑ p : κ × Bool, ((∑ j,bitSize (roundedMatrix A p j))+bitSize (roundedRhs b sign p)))+metadata ≤
      2*Fintype.card κ*(Fintype.card σ*tau+tau+Phi+2)+metadata :=
  Nat.add_le_add_right (rounded_cell_payload A b hell sign tau hA hb) metadata

theorem integer_rat_bits (a : ℤ) : ratBits (a:ℚ) = bitSize a+2 := by
  simp [ratBits]

theorem compressed_matrix_bits {σ κ : Type*} (A : κ → σ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) (p : κ × Bool) (j : σ) :
    ratBits (chamberMatrix A sign (.inl p) j) = bitSize (A p.1 j)+2 := by
  change ratBits (if p.2 then -(A p.1 j:ℚ) else (A p.1 j:ℚ)) = _
  split
  · rw [rat_neg_bits,integer_rat_bits]
  · exact integer_rat_bits _

theorem rational_cell_payload {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (tau : ℕ)
    (hA : ∀ i j,bitSize (A i j) ≤ tau) (hb : ∀ i,bitSize (b i) ≤ tau) :
    (∑ p : κ × Bool, ((∑ j,ratBits (chamberMatrix A sign (.inl p) j))+
      ratBits (compressedRhs b sign p))) ≤
      2*Fintype.card κ*(Fintype.card σ*(tau+2)+tau+Phi+4*ell.size+15) := by
  classical
  calc
    _ ≤ ∑ _p : κ × Bool, (Fintype.card σ*(tau+2)+tau+Phi+4*ell.size+15) := by
      apply Finset.sum_le_sum
      intro p _
      have hm : (∑ j,ratBits (chamberMatrix A sign (.inl p) j)) ≤ Fintype.card σ*(tau+2) := by
        calc
          _ ≤ ∑ _j : σ, (tau+2) := Finset.sum_le_sum (fun j _ => by rw [compressed_matrix_bits]; exact Nat.add_le_add_right (hA _ _) 2)
          _ = _ := by simp
      have hr := compressed_rhs_bits hell sign b p
      have := hb p.1
      omega
    _ = _ := by simp [Fintype.card_prod]; ring

/-- A common-margin column adds one rational 1 (four bits) to each row. -/
theorem margin_column_payload {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℚ) :
    (∑ i, ∑ j : Option σ, ratBits (match j with | none => 1 | some j => A i j)) =
    (∑ i, ∑ j, ratBits (A i j))+4*Fintype.card κ := by
  classical
  have hone : ratBits 1=4 := by decide
  simp [Fintype.sum_option,hone,Finset.sum_add_distrib]
  omega

/-- The two extra rows are -delta ≤ 0 and delta ≤ 1. -/
theorem margin_bound_rows_payload (σ : Type*) [Fintype σ] :
    (∑ u : Bool, ((∑ _j : σ,ratBits 0)+ratBits (if u then 1 else -1)+
      ratBits (if u then 1 else 0))) = 6*Fintype.card σ+15 := by
  have h0 : ratBits 0=3 := by decide
  have h1 : ratBits 1=4 := by decide
  have hn : ratBits (-1)=4 := by decide
  simp [h0,h1,hn]
  ring

theorem endpoint_den_divides (Phi ell : ℕ) (hell : 0<ell) (t : Endpoint Phi ell) :
    (endpointRat t).den ∣ 4*ell := by
  obtain ⟨n,_,he⟩ := endpoint_fraction Phi ell hell t
  obtain ⟨c,_,hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den (n:ℤ)
    (show ((4*ell:ℕ):ℤ) ≠ 0 by omega)
  have h := congrArg Int.natAbs hd
  simp only [Int.natAbs_mul,Int.natAbs_natCast,Int.cast_natCast] at h
  rw [he]
  refine ⟨c.natAbs, ?_⟩
  simpa [mul_comm] using h

theorem chamber_integer_encoding {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hne : (slackChamber A b Phi ell sign).Nonempty) (z : σ → ℤ) :
    (fun j => (z j:ℝ)) ∈ closure (slackChamber A b Phi ell sign) ↔
      ∀ p, ∑ j,roundedMatrix A p j*z j ≤ roundedRhs b sign p := by
  rw [chamber_integer_tests A b Phi ell sign hne z,rounded_system]

/-- A dense LP schema: row/column counts, each augmented row length,
objective-vector length, and one maximization-direction bit. -/
def lpMetadata (m d : ℕ) : ℕ :=
  bitSize ((2*m+2:ℕ):ℤ)+bitSize ((d+1:ℕ):ℤ)+
  (2*m+2)*bitSize ((d+2:ℕ):ℤ)+bitSize ((d+1:ℕ):ℤ)+1

noncomputable def lpMatrix {σ κ : Type*} (A : κ → σ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) :
    ((κ × Bool) ⊕ Bool) → Option σ → ℚ
  | .inl _, none => 1
  | .inl p, some j => chamberMatrix A sign (.inl p) j
  | .inr u, none => if u then 1 else -1
  | .inr _, some _ => 0

noncomputable def lpRhs {κ : Type*} (b : κ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) : ((κ × Bool) ⊕ Bool) → ℚ
  | .inl p => compressedRhs b sign p
  | .inr u => if u then 1 else 0

def lpObjective {σ : Type*} : Option σ → ℚ
  | none => 1
  | some _ => 0

noncomputable def lpEncoding {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) : ℕ :=
  (∑ i, ((∑ j,ratBits (lpMatrix A sign i j))+ratBits (lpRhs b sign i)))+
  (∑ j : Option σ,ratBits (lpObjective j)) + lpMetadata (Fintype.card κ) (Fintype.card σ)

theorem lp_encoding_identity {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) :
    lpEncoding A b sign =
      (∑ p : κ × Bool, ((∑ j,ratBits (chamberMatrix A sign (.inl p) j))+
        ratBits (compressedRhs b sign p)))+
      8*Fintype.card κ+9*Fintype.card σ+19+
      lpMetadata (Fintype.card κ) (Fintype.card σ) := by
  classical
  have h0 : ratBits 0=3 := by decide
  have h1 : ratBits 1=4 := by decide
  have hn : ratBits (-1)=4 := by decide
  simp [lpEncoding,lpMatrix,lpRhs,lpObjective,Fintype.sum_sum_type,
    Fintype.sum_option,Finset.sum_add_distrib,h0,h1,hn,Fintype.card_prod]
  ring

theorem complete_lp_encoding {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) {Phi ell : ℕ} (hell : 0<ell)
    (sign : (κ × Endpoint Phi ell) → Bool) (tau : ℕ)
    (hA : ∀ i j,bitSize (A i j) ≤ tau) (hb : ∀ i,bitSize (b i) ≤ tau) :
    lpEncoding A b sign ≤
      2*Fintype.card κ*(Fintype.card σ*(tau+2)+tau+Phi+4*ell.size+15)+
      8*Fintype.card κ+9*Fintype.card σ+19+
      lpMetadata (Fintype.card κ) (Fintype.card σ) := by
  rw [lp_encoding_identity]
  have := rational_cell_payload A b hell sign tau hA hb
  omega

theorem natural_size_le (n : ℕ) : n.size ≤ n := by
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

theorem lp_metadata_bound (m d : ℕ) :
    lpMetadata m d ≤ (2*m+2)*(d+3)+2*m+2*d+8 := by
  have h1 := natural_size_le (2*m+2)
  have h2 := natural_size_le (d+1)
  have h3 := natural_size_le (d+2)
  unfold lpMetadata bitSize
  simp only [Int.natAbs_natCast]
  have hm := Nat.mul_le_mul_left (2*m+2) h3
  nlinarith

/-- The actual refinement has polynomial bit length even when 1/epsilon is large. -/
theorem refinement_size (D a q : ℕ) (hD : 0<D) (ha : 0<a) (hq : 0<q) :
    (max (D^2) ⌈(D:ℝ)/Real.sqrt ((a:ℝ)/q)⌉₊).size ≤ 2*D.size+q.size := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hs := Real.sq_sqrt (le_of_lt (div_pos haR hqR))
  have hp := Real.sqrt_pos.2 (div_pos haR hqR)
  have he : (Real.sqrt ((a:ℝ)/q))^2*(q:ℝ) = a := by rw [hs]; field_simp
  have haq : (1:ℝ) ≤ (a:ℝ)*q := by exact_mod_cast (show 1 ≤ a*q by nlinarith)
  have hs1 : 1 ≤ Real.sqrt ((a:ℝ)/q)*(q:ℝ) := by
    have he' : (Real.sqrt ((a:ℝ)/q)*(q:ℝ))^2 = (a:ℝ)*q := by nlinarith [he]
    nlinarith [sq_nonneg (Real.sqrt ((a:ℝ)/q)*(q:ℝ)-1)]
  have hc : ⌈(D:ℝ)/Real.sqrt ((a:ℝ)/q)⌉₊ ≤ D*q := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hp).mpr
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hs1 (show (0:ℝ)≤D by positivity)]
  have hb : max (D^2) ⌈(D:ℝ)/Real.sqrt ((a:ℝ)/q)⌉₊ ≤ D^2*q := by
    apply max_le
    · nlinarith
    · have := Nat.mul_le_mul_right q (show D≤D^2 by nlinarith)
      omega
  have hbits := Nat.size_le_size hb
  have hm := size_mul_le (D^2) q
  have hd := size_mul_le D D
  rw [pow_two] at hm hbits ⊢
  omega

theorem chkm_phi_polynomial (d tau phi : ℕ) (hd : d≤phi) (ht : tau≤phi+1) :
    chkmPhi d tau ≤ 42*(phi+1)^4 := by
  unfold chkmPhi
  have h : 5*d^2*((d+1)*(tau+3)) ≤ 5*phi^2*((phi+1)*(phi+1+3)) := by gcongr
  nlinarith [Nat.zero_le (phi^3),Nat.zero_le (phi^4)]

/-- A concrete polynomial majorant, not an asymptotic-cost assumption. -/
theorem lp_bound_polynomial (m d T Phi ell phi : ℕ)
    (hm : m≤phi) (hd : d≤phi) (hT : T≤phi+1)
    (hPhi : Phi≤42*(phi+1)^4) (hell : ell.size≤3*phi) :
    2*m*(d*(T+2)+T+Phi+4*ell.size+15)+8*m+9*d+19+lpMetadata m d ≤
      200*(phi+1)^5 := by
  have hmeta := lp_metadata_bound m d
  have hp :
      2*m*(d*(T+2)+T+Phi+4*ell.size+15)+8*m+9*d+19+
        ((2*m+2)*(d+3)+2*m+2*d+8) ≤
      2*phi*(phi*(phi+1+2)+(phi+1)+42*(phi+1)^4+4*(3*phi)+15)+
        8*phi+9*phi+19+((2*phi+2)*(phi+3)+2*phi+2*phi+8) := by gcongr
  nlinarith [Nat.zero_le (phi^2),Nat.zero_le (phi^3),Nat.zero_le (phi^4),Nat.zero_le (phi^5)]

theorem complete_lp_polynomial {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (phi D a q tau : ℕ)
    (hm : Fintype.card κ≤phi) (hd : Fintype.card σ≤phi) (ht : tau≤phi+1)
    (hD : 0<D) (ha : 0<a) (hq : 0<q) (hDb : D.size≤phi) (hqb : q.size≤phi)
    (hA : ∀ i j,bitSize (A i j) ≤ phi+1) (hb : ∀ i,bitSize (b i) ≤ phi+1)
    (sign : (κ × Endpoint (chkmPhi (Fintype.card σ) tau)
      (max (D^2) ⌈(D:ℝ)/Real.sqrt ((a:ℝ)/q)⌉₊)) → Bool) :
    lpEncoding A b sign ≤ 200*(phi+1)^5 := by
  have hell : 0 < max (D^2) ⌈(D:ℝ)/Real.sqrt ((a:ℝ)/q)⌉₊ :=
    lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hr := refinement_size D a q hD ha hq
  exact (complete_lp_encoding A b hell sign (phi+1) hA hb).trans
    (lp_bound_polynomial _ _ _ _ _ phi hm hd le_rfl
      (chkm_phi_polynomial _ _ _ hd ht) (by omega))

/-- Relate the unary degree convention to the input-size bound used above. -/
theorem unary_degree_size (D phi : ℕ) (h : D≤phi) : D.size≤phi :=
  (natural_size_le D).trans h

/-- Cleared entries have linear length in the original rational row payload. -/
theorem cleared_entry_input_bound {σ : Type*} [Fintype σ] [DecidableEq σ]
    (v : σ → ℚ) (phi : ℕ) (h : rationalPayload v≤phi) (i : σ) :
    bitSize (clearedEntry v i) ≤ phi+1 := by
  have hi : bitSize (v i).num ≤ ∑ j, bitSize (v j).num :=
    Finset.single_le_sum (f := fun j => bitSize (v j).num) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc := clearedEntry_bits v i
  unfold rationalPayload at h
  omega

/-- The numerical log parameter used in the manuscript is linearly bounded. -/
theorem coefficient_log_bound (M phi : ℕ) (hphi : 0<phi) (hM : M<2^phi) :
    Nat.clog 2 (2+M) ≤ phi+1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  have hp : 2 ≤ (2:ℕ)^phi := by
    simpa using Nat.pow_le_pow_right (by decide : 1≤2) hphi
  rw [pow_succ]
  omega

/-- Rounded feasibility queries admit the same conservative polynomial bound. -/
theorem rounded_cell_polynomial {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (phi tau ell : ℕ) (hell : 0<ell)
    (hm : Fintype.card κ≤phi) (hd : Fintype.card σ≤phi) (ht : tau≤phi+1)
    (hA : ∀ i j,bitSize (A i j) ≤ phi+1) (hb : ∀ i,bitSize (b i) ≤ phi+1)
    (sign : (κ × Endpoint (chkmPhi (Fintype.card σ) tau) ell) → Bool) :
    (∑ p : κ × Bool, ((∑ j,bitSize (roundedMatrix A p j))+bitSize (roundedRhs b sign p)))+
      lpMetadata (Fintype.card κ) (Fintype.card σ) ≤ 200*(phi+1)^5 := by
  have h := rounded_cell_encoding A b hell sign (phi+1)
    (lpMetadata (Fintype.card κ) (Fintype.card σ)) hA hb
  have hp := lp_bound_polynomial (Fintype.card κ) (Fintype.card σ) (phi+1)
    (chkmPhi (Fintype.card σ) tau) 0 phi hm hd le_rfl
    (chkm_phi_polynomial _ _ _ hd ht) (by simp)
  have hmul : Fintype.card σ*(phi+1) ≤ Fintype.card σ*(phi+1+2) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

end CellEncoding
