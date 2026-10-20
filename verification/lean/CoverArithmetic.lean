import ScaledPolynomial
import Mathlib.Data.Nat.Choose.Sum

namespace CoverArithmetic

def chkmPhi (d tau : ℕ) : ℕ := 5*d^2*((d+1)*(tau+3))+2

/-- Elementary absorption used only to translate the published estimates. -/
theorem dimension_pow (d : ℕ) : d+1 ≤ 2^d := by
  induction d with
  | zero => norm_num
  | succ d ih => rw [pow_succ]; omega

theorem chkm_coordinate_absorption (d F : ℕ) (hd : 2 ≤ d) (hF : 1 ≤ F) :
    ((d:ℝ)+1)*2^(2*(d+1)^2*F) < (2:ℝ)^(5*d^2*F+2) := by
  have hc : (d:ℝ)+1 ≤ (2:ℝ)^d := by exact_mod_cast dimension_pow d
  have he : d+2*(d+1)^2*F ≤ 5*d^2*F := by
    have h : 2*(d+1)^2+d ≤ 5*d^2 := by nlinarith
    nlinarith
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
  have hm := mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ 2^(2*(d+1)^2*F))
  rw [← pow_add] at hm
  have hpos : (0:ℝ) < 2^(5*d^2*F) := by positivity
  rw [pow_add]; norm_num
  linarith

theorem chkm_slack_absorption (d F : ℕ) (hd : 2 ≤ d) (hF : 1 ≤ F) :
    ((2:ℝ)^(d*F)+(d:ℝ)*(d+1)*2^((d+2*(d+1)^2)*F))/2 <
      (2:ℝ)^(5*d^2*F+2) := by
  by_cases htwo : d=2
  · subst d
    norm_num
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 2*F ≤ 20*F by omega)
    have hp : (0:ℝ)<2^(20*F) := by positivity
    rw [pow_add]; norm_num
    nlinarith
  · have hd3 : 3 ≤ d := by omega
    have hc : (d:ℝ)+1 ≤ (2:ℝ)^d := by exact_mod_cast dimension_pow d
    have hc2 : (d:ℝ)*(d+1) ≤ (2:ℝ)^(2*d) := by
      rw [show 2*d=d+d by omega, pow_add]
      nlinarith [show (0:ℝ) ≤ d by positivity]
    have he : 2*d+(d+2*(d+1)^2)*F ≤ 5*d^2*F := by
      have h : 2*d+(d+2*(d+1)^2) ≤ 5*d^2 := by nlinarith
      nlinarith
    have hm := mul_le_mul_of_nonneg_right hc2
      (by positivity : (0:ℝ) ≤ 2^((d+2*(d+1)^2)*F))
    rw [← pow_add] at hm
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
    have hsmall : d*F ≤ 5*d^2*F := by nlinarith
    have hs := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hsmall
    have hpos : (0:ℝ)<2^(5*d^2*F) := by positivity
    rw [pow_add]; norm_num
    linarith

/-- CHKM coordinate and doubled shifted-slack estimates are explicit hypotheses.
No theorem about the integer hull or its vertices is assumed as a Lean axiom. -/
theorem chkm_vertex_bounds (d tau : ℕ) (x s : ℝ) (hd : 2 ≤ d)
    (hx : |x| ≤ (d+1:ℝ)*2^(2*(d+1)^2*((d+1)*(tau+3))))
    (hs : 2*s ≤ (2:ℝ)^(d*((d+1)*(tau+3)))+
      (d:ℝ)*(d+1)*2^((d+2*(d+1)^2)*((d+1)*(tau+3)))) :
    |x| < (2:ℝ)^chkmPhi d tau ∧ s < (2:ℝ)^chkmPhi d tau := by
  have hF : 1 ≤ (d+1)*(tau+3) := by nlinarith
  constructor
  · exact hx.trans_lt (chkm_coordinate_absorption d _ hd hF)
  · have h := chkm_slack_absorption d ((d+1)*(tau+3)) hd hF
    unfold chkmPhi
    linarith


/-- Convex-combination assembly. Vertex representations, the published CHKM
estimates, and the half-unit slack gap are the external geometric inputs. -/
theorem chkm_convex_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d tau : ℕ) (v s w : ι → ℝ) (hd : 2 ≤ d)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1)
    (hv : ∀ i, |v i| ≤ (d+1:ℝ)*2^(2*(d+1)^2*((d+1)*(tau+3))))
    (hs : ∀ i, 2*s i ≤ (2:ℝ)^(d*((d+1)*(tau+3)))+
      (d:ℝ)*(d+1)*2^((d+2*(d+1)^2)*((d+1)*(tau+3))))
    (hgap : ∀ i, 1/2 ≤ s i) :
    |∑ i, w i*v i| < (2:ℝ)^chkmPhi d tau ∧
    1/2 ≤ ∑ i, w i*s i ∧ ∑ i, w i*s i < (2:ℝ)^chkmPhi d tau := by
  have hb := fun i => chkm_vertex_bounds d tau (v i) (s i) hd (hv i) (hs i)
  constructor
  · exact ScaledPolynomial.convex_coordinate_bound w v _ hw hsum (fun i => (hb i).1)
  constructor
  · calc
      (1:ℝ)/2 = ∑ i, w i*(1/2) := by rw [← Finset.sum_mul, hsum]; norm_num
      _ ≤ _ := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hgap i) (hw i))
  · apply lt_of_le_of_lt (le_abs_self _) (ScaledPolynomial.convex_coordinate_bound w s _ hw hsum ?_)
    intro i
    rw [abs_of_nonneg (by linarith [hgap i])]
    exact (hb i).2

/-- The one-dimensional case uses the elementary interval coordinate bound;
CHKM's higher-dimensional estimates are not applied at d=1. -/
theorem one_dimensional_bounds (tau : ℕ) (a b x : ℝ)
    (ha : |a| ≤ (2:ℝ)^tau) (hb : |b| ≤ (2:ℝ)^tau)
    (hx : |x| ≤ (2:ℝ)^tau) (hfeas : a*x ≤ b) :
    |x| < (2:ℝ)^chkmPhi 1 tau ∧
    1/2 ≤ b+1/2-a*x ∧ b+1/2-a*x < (2:ℝ)^chkmPhi 1 tau := by
  have hC : (1:ℝ) ≤ 2^tau := one_le_pow₀ (by norm_num)
  have hp : |a*x| ≤ (2:ℝ)^tau*2^tau := by
    rw [abs_mul]; exact mul_le_mul ha hx (abs_nonneg _) (by positivity)
  have he : 2*tau+3 ≤ chkmPhi 1 tau := by unfold chkmPhi; norm_num; omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) he
  have heq : (2:ℝ)^(2*tau+3) = 8*((2:ℝ)^tau*2^tau) := by
    rw [pow_add, show 2*tau=tau+tau by omega, pow_add]; norm_num; ring
  rw [heq] at hpow
  constructor
  · nlinarith
  constructor
  · linarith
  · have h1 := le_abs_self b
    have h2 := neg_le_abs (a*x)
    nlinarith

/-- Shift the dyadic level index by two, avoiding negative exponents. -/
noncomputable def threshold (ell k j : ℕ) : ℝ := (2:ℝ)^k/4*(1+(j:ℝ)/ell)

theorem threshold_end (ell k : ℕ) (hell : 0 < ell) :
    threshold ell k ell = (2:ℝ)^(k+1)/4 := by
  unfold threshold
  have h : (ell:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hell
  rw [div_self h, pow_succ]; ring

theorem threshold_width (ell k j : ℕ) (hell : 0 < ell) :
    threshold ell k (j+1)-threshold ell k j ≤ threshold ell k j / ell := by
  have he : (0:ℝ)<ell := by exact_mod_cast hell
  have hj : (0:ℝ) ≤ (j:ℝ)/ell := by positivity
  unfold threshold
  push_cast
  have hp : (0:ℝ)<2^k/4 := by positivity
  field_simp
  nlinarith

theorem dyadic_band (L : ℕ) (s : ℝ) (hs : 1/4 ≤ s)
    (ht : s < (2:ℝ)^L/4) :
    ∃ k < L, (2:ℝ)^k/4 ≤ s ∧ s < (2:ℝ)^(k+1)/4 := by
  induction L with
  | zero => norm_num at ht; linarith
  | succ L ih =>
    by_cases h : s < (2:ℝ)^L/4
    · obtain ⟨k,hk,ha,hb⟩ := ih h
      exact ⟨k,by omega,ha,hb⟩
    · exact ⟨L,by omega,le_of_not_gt h,ht⟩

theorem refined_band (ell k : ℕ) (s : ℝ) (hell : 0 < ell)
    (hs : (2:ℝ)^k/4 ≤ s) (ht : s < (2:ℝ)^(k+1)/4) :
    ∃ j < ell, threshold ell k j ≤ s ∧ s < threshold ell k (j+1) := by
  have he : (0:ℝ)<ell := by exact_mod_cast hell
  have hp : (0:ℝ)<2^k/4 := by positivity
  let u : ℝ := (s / ((2:ℝ)^k/4)-1)*ell
  have hu : 0 ≤ u := by
    dsimp [u]
    have h : 1 ≤ s/((2:ℝ)^k/4) := (le_div_iff₀ hp).2 (by simpa using hs)
    positivity
  have hu' : u < ell := by
    have ht' : s < 2*((2:ℝ)^k/4) := by rw [pow_succ] at ht; nlinarith
    have h : s/((2:ℝ)^k/4) < 2 := (div_lt_iff₀ hp).2 (by linarith)
    dsimp [u]; nlinarith
  have hid : s = ((2:ℝ)^k/4)*(1+u/ell) := by
    dsimp [u]
    field_simp
    ring
  refine ⟨⌊u⌋₊, (Nat.floor_lt hu).2 hu', ?_, ?_⟩
  · have h := div_le_div_of_nonneg_right (Nat.floor_le hu) he.le
    unfold threshold
    rw [hid]
    exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  · have h := (div_lt_div_iff_of_pos_right he).2 (Nat.lt_floor_add_one u)
    unfold threshold
    push_cast
    rw [hid]
    exact mul_lt_mul_of_pos_left (by linarith) hp


noncomputable def thresholds (Phi ell : ℕ) : Finset ℝ := by
  classical
  exact insert ((2:ℝ)^Phi) ((Finset.range (Phi+2) ×ˢ Finset.range ell).image
    (fun kj => threshold ell kj.1 kj.2))

theorem threshold_mem (Phi ell k j : ℕ) (hk : k<Phi+2) (hj : j<ell) :
    threshold ell k j ∈ thresholds Phi ell := by
  classical
  simp only [thresholds, Finset.mem_insert, Finset.mem_image, Finset.mem_product,
    Finset.mem_range]
  exact Or.inr ⟨(k,j),⟨hk,hj⟩,rfl⟩

theorem final_threshold (Phi : ℕ) : (2:ℝ)^(Phi+2)/4 = (2:ℝ)^Phi := by
  rw [pow_add]; norm_num

theorem upper_threshold_mem (Phi ell k j : ℕ) (hell : 0<ell)
    (hk : k<Phi+2) (hj : j<ell) :
    threshold ell k (j+1) ∈ thresholds Phi ell := by
  classical
  by_cases h : j+1<ell
  · exact threshold_mem Phi ell k (j+1) hk h
  · have heq : j+1=ell := by omega
    rw [heq, threshold_end ell k hell]
    by_cases hk' : k+1<Phi+2
    · have hzero : threshold ell (k+1) 0 = (2:ℝ)^(k+1)/4 := by simp [threshold]
      rw [← hzero]
      exact threshold_mem Phi ell (k+1) 0 hk' hell
    · have he : k+1=Phi+2 := by omega
      rw [he, final_threshold]
      simp [thresholds]

/-- Actual finite thresholds cover every relevant slack by a closed interval
of the required relative width. Endpoint membership is proved, not assumed. -/
theorem threshold_coverage (Phi ell : ℕ) (s : ℝ) (hell : 0<ell)
    (hs : 1/4 ≤ s) (ht : s < (2:ℝ)^Phi) :
    ∃ a ∈ thresholds Phi ell, ∃ c ∈ thresholds Phi ell,
      0<a ∧ a ≤ s ∧ s ≤ c ∧ c-a ≤ a/ell := by
  have ht' : s < (2:ℝ)^(Phi+2)/4 := by rwa [final_threshold]
  obtain ⟨k,hk,hlo,hhi⟩ := dyadic_band (Phi+2) s (by linarith) ht'
  obtain ⟨j,hj,ha,hc⟩ := refined_band ell k s hell hlo hhi
  refine ⟨_,threshold_mem Phi ell k j hk hj,_,upper_threshold_mem Phi ell k j hell hk hj,
    ?_,ha,hc.le,threshold_width ell k j hell⟩
  unfold threshold
  positivity

theorem threshold_count (Phi ell : ℕ) :
    (thresholds Phi ell).card ≤ (Phi+2)*ell+1 := by
  classical
  unfold thresholds
  calc
    _ ≤ ((Finset.range (Phi+2) ×ˢ Finset.range ell).image
        (fun kj => threshold ell kj.1 kj.2)).card+1 := Finset.card_insert_le _ _
    _ ≤ (Finset.range (Phi+2) ×ˢ Finset.range ell).card+1 :=
      Nat.add_le_add_right (Finset.card_image_le) 1
    _ = _ := by simp

/-- The scalar interval coverage assembles rowwise for any finite row set.
This is not a formalization of hyperplane-chamber construction. -/
theorem rowwise_threshold_coverage {ι : Type*} (Phi ell : ℕ) (s : ι → ℝ)
    (hell : 0<ell) (hs : ∀ i, 1/4 ≤ s i) (ht : ∀ i, s i < (2:ℝ)^Phi) :
    ∃ a c : ι → ℝ, ∀ i, a i ∈ thresholds Phi ell ∧ c i ∈ thresholds Phi ell ∧
      0<a i ∧ a i ≤ s i ∧ s i ≤ c i ∧ c i-a i ≤ a i/ell := by
  classical
  have h := fun i => threshold_coverage Phi ell (s i) hell (hs i) (ht i)
  choose a ha c hc hb using h
  exact ⟨a,c,fun i => ⟨ha i,hc i,hb i⟩⟩

def chamberBound (H d : ℕ) : ℕ := ∑ j ∈ Finset.range (d+1), H.choose j

theorem chamber_zero_dimension (H : ℕ) : chamberBound H 0=1 := by
  simp [chamberBound]

theorem chamber_zero_hyperplanes (d : ℕ) : chamberBound 0 d=1 := by
  induction d with
  | zero => simp [chamber_zero_dimension]
  | succ d ih =>
    unfold chamberBound at *
    rw [Finset.sum_range_succ]
    simp [Nat.choose_eq_zero_of_lt (by omega : 0<d+1), ih]

theorem chamber_recurrence (H d : ℕ) :
    chamberBound (H+1) (d+1)=chamberBound H (d+1)+chamberBound H d := by
  unfold chamberBound
  have split (n : ℕ) : (∑ j ∈ Finset.range (d+1+1), n.choose j) =
      (∑ j ∈ Finset.range (d+1), n.choose (j+1))+1 := by
    rw [Finset.sum_range_succ']; simp
  rw [split (H+1), split H]
  simp only [Nat.choose_succ_succ', Finset.sum_add_distrib]
  omega

theorem chamber_power_bound (H d : ℕ) : chamberBound H d ≤ (1+H)^d := by
  induction d with
  | zero => simp [chamber_zero_dimension]
  | succ d ih =>
    have he : chamberBound H (d+1) = chamberBound H d + H.choose (d+1) := by
      unfold chamberBound; rw [Finset.sum_range_succ]
    rw [he]
    have hc := Nat.choose_le_pow H (d+1)
    have hp : H^d ≤ (1+H)^d := Nat.pow_le_pow_left (by omega) d
    rw [pow_succ] at hc ⊢
    nlinarith

/-- The geometric insertion estimate is a hypothesis; induction and binomial
arithmetic are verified here. -/
theorem insertion_count_bound (N : ℕ → ℕ → ℕ)
    (hzero : ∀ d, N 0 d ≤ 1) (hdzero : ∀ H, N H 0 ≤ 1)
    (hstep : ∀ H d, N (H+1) (d+1) ≤ N H (d+1)+N H d) :
    ∀ H d, N H d ≤ chamberBound H d := by
  intro H
  induction H with
  | zero => intro d; simpa [chamber_zero_hyperplanes] using hzero d
  | succ H ih =>
    intro d
    cases d with
    | zero => simpa [chamber_zero_dimension] using hdzero (H+1)
    | succ d => rw [chamber_recurrence]; exact (hstep H d).trans (Nat.add_le_add (ih _) (ih _))

/-- At most one integer query per chamber and two LP tests per cell per
insertion, with allowance for an initial stage. -/
theorem oracle_and_lp_counts (H d oracle lp : ℕ)
    (ho : oracle ≤ chamberBound H d)
    (hl : lp ≤ 2*(H+1)*chamberBound H d) :
    oracle ≤ (H+1)^d ∧ lp ≤ 2*(H+1)^(d+1) := by
  have h := chamber_power_bound H d
  rw [Nat.add_comm 1 H] at h
  constructor
  · exact ho.trans h
  · calc
      lp ≤ 2*(H+1)*chamberBound H d := hl
      _ ≤ 2*(H+1)*(H+1)^d := Nat.mul_le_mul_left _ h
      _ = _ := by rw [pow_succ]; ring


/-- Substitute the actual threshold count into the hyperplane count. -/
theorem hyperplane_count (m Phi ell : ℕ) :
    m*(thresholds Phi ell).card ≤ m*((Phi+2)*ell+1) :=
  Nat.mul_le_mul_left m (threshold_count Phi ell)

theorem hyperplane_linear_refinement (m Phi ell : ℕ) (hell : 1 ≤ ell) :
    m*((Phi+2)*ell+1)+1 ≤ (m*(Phi+3)+1)*ell := by
  nlinarith

/-- The geometric oracle/LP count hypotheses give ell^d and ell^(d+1),
respectively. In particular their exponents differ by one refinement factor. -/
theorem refinement_query_counts (m Phi ell d oracle lp : ℕ) (hell : 1 ≤ ell)
    (ho : oracle ≤ chamberBound (m*((Phi+2)*ell+1)) d)
    (hl : lp ≤ 2*(m*((Phi+2)*ell+1)+1)*chamberBound (m*((Phi+2)*ell+1)) d) :
    oracle ≤ (m*(Phi+3)+1)^d*ell^d ∧
    lp ≤ 2*(m*(Phi+3)+1)^(d+1)*ell^(d+1) := by
  have h := oracle_and_lp_counts _ d oracle lp ho hl
  have hlin := hyperplane_linear_refinement m Phi ell hell
  constructor
  · exact h.1.trans (by simpa [mul_pow] using Nat.pow_le_pow_left hlin d)
  · calc
      lp ≤ 2*(m*((Phi+2)*ell+1)+1)^(d+1) := h.2
      _ ≤ 2*((m*(Phi+3)+1)*ell)^(d+1) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlin (d+1))
      _ = _ := by rw [mul_pow]; ring


/-- Translate an arbitrary published per-inequality size F bounded by our
encoding convention; monotonicity of all exponents is checked here. -/
theorem chkm_encoding_translation (d tau F : ℕ) (x s : ℝ) (hd : 2 ≤ d)
    (hF : F ≤ (d+1)*(tau+3))
    (hx : |x| ≤ (d+1:ℝ)*2^(2*(d+1)^2*F))
    (hs : 2*s ≤ (2:ℝ)^(d*F)+(d:ℝ)*(d+1)*2^((d+2*(d+1)^2)*F)) :
    |x| < (2:ℝ)^chkmPhi d tau ∧ s < (2:ℝ)^chkmPhi d tau := by
  apply chkm_vertex_bounds d tau x s hd
  · exact hx.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.mul_le_mul_left _ hF)) (by positivity))
  · apply hs.trans
    apply add_le_add
    · exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.mul_le_mul_left _ hF)
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.mul_le_mul_left _ hF)) (by positivity)

end CoverArithmetic
