import CoverArithmetic
import LineRestriction
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace CoverAssembly
open CoverArithmetic LineRestriction

abbrev Endpoint (Phi ell : ℕ) := {t : ℝ // t ∈ thresholds Phi ell}
abbrev Interval (Phi ell : ℕ) :=
  {p : Endpoint Phi ell × Endpoint Phi ell // 0 < p.1.val ∧ p.2.val-p.1.val ≤ p.1.val/ell}

noncomputable instance intervalFintype (Phi ell : ℕ) : Fintype (Interval Phi ell) := by
  classical
  infer_instance

noncomputable def slack {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (x : σ → ℝ) (i : κ) : ℝ :=
  (b i : ℝ)+1/2-integerRow (A i) x

def intervalCell {σ κ : Type*} [Fintype σ] {Phi ell : ℕ}
    (A : κ → σ → ℤ) (b : κ → ℤ) (c : κ → Interval Phi ell) : Set (σ → ℝ) :=
  {x | ∀ i, (c i).val.1.val ≤ slack A b x i ∧ slack A b x i ≤ (c i).val.2.val}

theorem interval_cover {σ κ : Type*} [Fintype σ] (Phi ell : ℕ)
    (A : κ → σ → ℤ) (b : κ → ℤ) (x : σ → ℝ) (hell : 0<ell)
    (hs : ∀ i, 1/4 ≤ slack A b x i) (ht : ∀ i, slack A b x i < (2:ℝ)^Phi) :
    ∃ c : κ → Interval Phi ell, x ∈ intervalCell A b c := by
  classical
  obtain ⟨a,c,ha⟩ := rowwise_threshold_coverage Phi ell (slack A b x) hell hs ht
  refine ⟨fun i => ⟨(⟨a i,(ha i).1⟩,⟨c i,(ha i).2.1⟩),
    (ha i).2.2.1,(ha i).2.2.2.2.2⟩, ?_⟩
  intro i
  exact ⟨(ha i).2.2.2.1,(ha i).2.2.2.2.1⟩

theorem interval_widths {σ κ : Type*} [Fintype σ] {Phi ell : ℕ}
    (A : κ → σ → ℤ) (b : κ → ℤ) (c : κ → Interval Phi ell)
    (u v : σ → ℝ) (hu : u ∈ intervalCell A b c) (hv : v ∈ intervalCell A b c) :
    ∀ i, ∃ lo hi : ℝ, hi-lo ≤ lo/ell ∧
      (lo ≤ slack A b u i ∧ slack A b u i ≤ hi) ∧
      (lo ≤ slack A b v i ∧ slack A b v i ≤ hi) := by
  intro i
  exact ⟨_,_,(c i).property.2,hu i,hv i⟩

/-- The cover and relative widths are conclusions for the finite family of
interval cells. Only feasible representatives, extrema and Markov remain inputs. -/
theorem interval_approximation {σ κ : Type*} [Fintype σ] [Fintype κ]
    (f : MvPolynomial σ ℝ) (A : κ → σ → ℤ) (b : κ → ℤ)
    (Y : Finset (σ → ℝ)) (x : σ → ℝ) (fmax eps : ℝ) (D Phi : ℕ)
    (hD : 0<D) (heps : 0<eps) (hdeg : f.totalDegree ≤ D)
    (hx : x ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ)
    (hbounds : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
      MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧ MvPolynomial.eval z f ≤ fmax)
    (hupper : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
      ∀ i, slack A b z i < (2:ℝ)^Phi)
    (hfeasible : ∀ y ∈ Y, y ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ)
    (hcomplete : ∀ c : κ → Interval Phi (max (D^2) ⌈(D:ℝ)/Real.sqrt eps⌉₊),
      (∃ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
        z ∈ intervalCell A b c) → ∃ y ∈ Y, y ∈ intervalCell A b c)
    (hmarkov : SampledMarkov.MarkovBound D (max (D^2) ⌈(D:ℝ)/Real.sqrt eps⌉₊)) :
    ∃ best ∈ Y, best ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f-MvPolynomial.eval x f ∧
      MvPolynomial.eval best f-MvPolynomial.eval x f ≤ eps*(fmax-MvPolynomial.eval x f) := by
  apply shifted_slack_cover_guarantee f A b (intervalCell (Phi:=Phi) A b) Y x fmax eps D
    hD heps hdeg hx hbounds ?_ hfeasible hcomplete hmarkov ?_
  · intro z hz
    apply interval_cover Phi _ A b z (FPTASCalculations.ceiling_refinement hD heps).1
    · intro i
      have h := shifted_slack_positive A b z hz.1 i
      dsimp [slack]
      linarith
    · exact hupper z hz
  · intro c u hu v hv
    simpa only [slack, Nat.cast_max, Nat.cast_pow] using interval_widths A b c u v hu hv


/-- Convexity supplies membership of the actual barycentric point. -/
theorem barycenter_mem {σ : Type*} {r : ℕ} (K : Set (σ → ℝ)) (hK : Convex ℝ K)
    (v0 : σ → ℝ) (v : Fin r → σ → ℝ) (a0 : ℝ) (a : Fin r → ℝ)
    (ha0 : 0 ≤ a0) (ha : ∀ i, 0 ≤ a i) (hs : a0+∑ i,a i=1)
    (hv0 : v0 ∈ K) (hv : ∀ i, v i ∈ K) :
    (fun j => a0*v0 j+∑ i,a i*v i j) ∈ K := by
  have h := hK.sum_mem (t:=Finset.univ) (w:=Fin.cons a0 a) (z:=Fin.cons v0 v)
    (fun i _ => by refine Fin.cases ha0 (fun i => ha i) i)
    (by simpa [Fin.sum_univ_succ] using hs)
    (fun i _ => by refine Fin.cases hv0 (fun i => hv i) i)
  convert h using 1
  ext j
  simp [Fin.sum_univ_succ, Finset.sum_apply]

/-- Assemble rounding, convex feasibility and the feasible-segment identity. -/
theorem rounded_barycenter_segment {σ : Type*} {r : ℕ}
    (K : Set (σ → ℝ)) (hK : Convex ℝ K) (v0 : σ → ℝ) (v : Fin r → σ → ℝ)
    (a0 k : ℝ) (a : Fin r → ℝ) (hr : 0<r) (hk : 0<k)
    (ha : ∀ i,0 ≤ a i) (hs : a0+∑ i,a i=1) (hlarge : 1 ≤ (r+1:ℝ)*a0)
    (hsize : (r:ℝ)*(r+1) ≤ k) (hv0 : v0 ∈ K) (hv : ∀ i,v i ∈ K) :
    let x := fun j => a0*v0 j+∑ i,a i*v i j
    let mu := fun i => (⌈k*a i⌉:ℝ)/k
    let y := fun j => (1-∑ i,mu i)*v0 j+∑ i,mu i*v i j
    let t := (r:ℝ)*(r+1)/k
    x ∈ K ∧ y ∈ K ∧ t ∈ Set.Icc (0:ℝ) 1 ∧
      ∃ w ∈ K, ∀ j, y j = x j+t*(w j-x j) := by
  dsimp
  have ha0 : 0≤a0 := by nlinarith [show (0:ℝ) ≤ r by positivity]
  obtain ⟨ht0,ht1,hm0,_,hmi⟩ := FPTASCalculations.rounded_barycentric_weights a a0 k hk ha hs hlarge hsize
  obtain ⟨w0,w,hw0,hw,hws,h0,hi⟩ := FPTASCalculations.rounded_segment_weights a a0 k hr hk ha hs hlarge hsize
  refine ⟨barycenter_mem K hK v0 v a0 a ha0 ha hs hv0 hv,
    barycenter_mem K hK v0 v _ _ hm0 (fun i => (hmi i).1) (by ring) hv0 hv,
    ⟨ht0,ht1⟩,fun j => w0*v0 j+∑ i,w i*v i j,
    barycenter_mem K hK v0 v w0 w hw0 hw hws hv0 hv,?_⟩
  intro j
  have h := FPTASCalculations.barycentric_coordinate_segment a
    (fun i => (⌈k*a i⌉:ℝ)/k) w (fun i => v i j)
    a0 (1-∑ i,(⌈k*a i⌉:ℝ)/k) w0 (v0 j) ((r:ℝ)*(r+1)/k) h0 hi
  nlinarith

/-- A multivariate polynomial on a feasible convex segment satisfies the
classical interval-Markov error estimate, without an assumed error bound. -/
theorem polynomial_segment_error {σ : Type*} (K : Set (σ → ℝ)) (hK : Convex ℝ K)
    (f : MvPolynomial σ ℝ) (x w y : σ → ℝ) (D : ℕ) (t R : ℝ)
    (hx : x ∈ K) (hw : w ∈ K) (ht : t ∈ Set.Icc (0:ℝ) 1)
    (hy : ∀ j, y j=x j+t*(w j-x j)) (hdeg : f.totalDegree ≤ D)
    (hb : ∀ z ∈ K, 0 ≤ MvPolynomial.eval z f-MvPolynomial.eval x f ∧
       MvPolynomial.eval z f-MvPolynomial.eval x f ≤ R)
    (hm : SampledMarkov.IntervalMarkovBound D 0 1) :
    |MvPolynomial.eval y f-MvPolynomial.eval x f| ≤ 2*(D:ℝ)^2*t*R := by
  let p := restrict f x w-Polynomial.C (MvPolynomial.eval x f)
  have hpd : p.natDegree ≤ D := by
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((degree_restrict f x w).trans hdeg) (by simp))
  have hpb : ∀ u ∈ Set.Icc (0:ℝ) 1, |p.eval u| ≤ R := by
    intro u hu
    have hmem : (fun j => x j+u*(w j-x j)) ∈ K := by
      convert hK hx hw (sub_nonneg.mpr hu.2) hu.1 (by ring : 1-u+u=1) using 1
      ext j; simp; ring
    have h := hb _ hmem
    simpa [p, Polynomial.eval_sub, eval_restrict, abs_of_nonneg h.1] using h.2
  have h := SampledMarkov.unit_interval_markov_error p hpd R t hm hpb ht
  have hy' : (fun j => x j+t*(w j-x j))=y := by ext j; exact (hy j).symm
  simpa [p, Polynomial.eval_sub, eval_zero, eval_restrict, hy'] using h


noncomputable def roundedPoint {σ : Type*} {r : ℕ}
    (a : Fin r → ℝ) (v0 : σ → ℝ) (v : Fin r → σ → ℝ) (k : ℕ) : σ → ℝ :=
  fun j => (1-∑ i,(⌈(k:ℝ)*a i⌉:ℝ)/k)*v0 j+∑ i,((⌈(k:ℝ)*a i⌉:ℝ)/k)*v i j

theorem rounded_mixed_grid {σ : Type*} [Fintype σ] [DecidableEq σ] {r : ℕ}
    (I : Finset σ) (a : Fin r → ℝ) (v0 : σ → ℝ) (v : Fin r → σ → ℝ)
    (k Delta : ℕ) (hk : 0<k) (hDelta : 0<Delta)
    (hv0 : ∀ j ∈ I, ∃ z : ℤ,v0 j=(z:ℝ)/Delta)
    (hv : ∀ i j, j ∈ I → ∃ z : ℤ,v i j=(z:ℝ)/Delta)
    (hi0 : ∀ j, j ∉ I → ∃ z : ℤ,v0 j=z)
    (hi : ∀ i j, j ∉ I → v i j=v0 j) :
    ScaledPolynomial.integral (ScaledPolynomial.encode I ((k:ℤ)*Delta) (roundedPoint a v0 v k)) := by
  classical
  apply (ScaledPolynomial.grid_coordinates I _ (by positivity) _).2
  intro j
  by_cases hj : j ∈ I
  · obtain ⟨z0,hz0⟩ := hv0 j hj
    choose z hz using fun i => hv i j hj
    refine ⟨((k:ℤ)-∑ i,⌈(k:ℝ)*a i⌉)*z0+∑ i,⌈(k:ℝ)*a i⌉*z i,?_⟩
    simp only [if_pos hj, Int.cast_mul, Int.cast_natCast]
    unfold roundedPoint
    simp_rw [hz0,hz]
    exact FPTASCalculations.rounded_grid_coordinate a z z0 k Delta (ne_of_gt hk) (ne_of_gt hDelta)
  · obtain ⟨z,hz⟩ := hi0 j hj
    refine ⟨z,?_⟩
    simp only [if_neg hj, roundedPoint]
    simp_rw [hi _ j hj, ← Finset.sum_mul]
    rw [← hz]
    ring

noncomputable def gridMultiplier (D r : ℕ) (eps : ℝ) : ℕ :=
  ⌈4*(D:ℝ)^2*r*(r+1)/eps⌉₊

theorem natural_grid_budget (D r : ℕ) (eps : ℝ) (hD : 0<D) (hr : 0<r)
    (heps : 0<eps) (heps1 : eps ≤ 1) :
    0 < gridMultiplier D r eps ∧
    (r:ℝ)*(r+1) ≤ gridMultiplier D r eps ∧
    2*(D:ℝ)^2*((r:ℝ)*(r+1)/gridMultiplier D r eps) ≤ eps/2 := by
  have h := FPTASCalculations.markov_grid_multiplier (D:ℝ) (r:ℝ) eps
    (by exact_mod_cast hD) (by exact_mod_cast hr) heps heps1
  have he : (gridMultiplier D r eps:ℝ)=⌈4*(D:ℝ)^2*r*(r+1)/eps⌉ := by
    exact natCast_ceil_eq_intCast_ceil (by positivity)
  rw [← he] at h
  exact ⟨by exact_mod_cast h.1,h.2⟩

/-- Published slice scaling and Caratheodory data appear as vertex/grid and
weight hypotheses; feasibility, the segment, grid membership and error follow. -/
theorem mixed_rounding_near {σ : Type*} [Fintype σ] [DecidableEq σ] {r : ℕ}
    (K : Set (σ → ℝ)) (hK : Convex ℝ K) (f : MvPolynomial σ ℝ)
    (I : Finset σ) (v0 : σ → ℝ) (v : Fin r → σ → ℝ)
    (a0 : ℝ) (a : Fin r → ℝ) (x : σ → ℝ) (D Delta : ℕ) (R eps : ℝ)
    (hD : 0<D) (hr : 0<r) (hDelta : 0<Delta) (heps : 0<eps) (heps1 : eps ≤ 1)
    (ha : ∀ i,0 ≤ a i) (hs : a0+∑ i,a i=1) (hlarge : 1 ≤ (r+1:ℝ)*a0)
    (hxrep : ∀ j,x j=a0*v0 j+∑ i,a i*v i j)
    (hv0K : v0 ∈ K) (hvK : ∀ i,v i ∈ K)
    (hv0 : ∀ j ∈ I, ∃ z : ℤ,v0 j=(z:ℝ)/Delta)
    (hv : ∀ i j, j ∈ I → ∃ z : ℤ,v i j=(z:ℝ)/Delta)
    (hi0 : ∀ j, j ∉ I → ∃ z : ℤ,v0 j=z)
    (hi : ∀ i j, j ∉ I → v i j=v0 j)
    (hdeg : f.totalDegree ≤ D)
    (hb : ∀ z ∈ K, 0 ≤ MvPolynomial.eval z f-MvPolynomial.eval x f ∧
       MvPolynomial.eval z f-MvPolynomial.eval x f ≤ R)
    (hm : SampledMarkov.IntervalMarkovBound D 0 1) :
    ∃ y ∈ K, ScaledPolynomial.integral
      (ScaledPolynomial.encode I ((gridMultiplier D r eps:ℤ)*Delta) y) ∧
      |MvPolynomial.eval y f-MvPolynomial.eval x f| ≤ (eps/2)*R := by
  let k := gridMultiplier D r eps
  obtain ⟨hk,hsize,hbudget⟩ := natural_grid_budget D r eps hD hr heps heps1
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hxid : (fun j => a0*v0 j+∑ i,a i*v i j)=x := by ext j; exact (hxrep j).symm
  obtain ⟨hxK,hyK,ht,w,hwK,hy⟩ := rounded_barycenter_segment K hK v0 v a0 k a hr hkr ha hs hlarge hsize hv0K hvK
  rw [hxid] at hxK hy
  have herr := polynomial_segment_error K hK f x w (roundedPoint a v0 v k) D _ R
    hxK hwK ht hy hdeg hb hm
  have hR : 0 ≤ R := by have h := hb x hxK; simpa using h.2
  exact ⟨roundedPoint a v0 v k,hyK,rounded_mixed_grid I a v0 v k Delta hk hDelta hv0 hv hi0 hi,
    herr.trans (mul_le_mul_of_nonneg_right hbudget hR)⟩


/-- Finite proper affine hyperplanes have dense complement. -/
theorem avoid_hyperplanes_dense {σ ι : Type*} [Fintype σ] [Fintype ι]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (hcont : ∀ i, Continuous (L i)) (hproper : ∀ i, ∃ v, L i v ≠ 0) :
    Dense {x | ∀ i,L i x ≠ a i} := by
  have hd : ∀ i,Dense {x | L i x ≠ a i} := by
    intro i
    obtain ⟨v,hv⟩ := hproper i
    have hsurj : Function.Surjective (L i) := by
      intro t
      refine ⟨(t/L i v) • v,?_⟩
      simp [map_smul, hv]
    exact (dense_compl_singleton (a i)).preimage
      (IsModuleTopology.isOpenMap_of_surjective hsurj)
  have ho : ∀ i, IsOpen {x | L i x ≠ a i} := by
    intro i
    exact isOpen_ne_fun (hcont i) continuous_const
  simpa only [Set.ofPred_forall] using dense_iInter_of_isOpen ho hd

def strictRegion {σ ι : Type*} (U : Set (σ → ℝ))
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) (sign : ι → Bool) : Set (σ → ℝ) :=
  {x | x ∈ U ∧ ∀ i, if sign i then L i x < a i else a i < L i x}

theorem strictRegion_open {σ ι : Type*} [Fintype σ] [Fintype ι]
    (U : Set (σ → ℝ)) (hU : IsOpen U) (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ)
    (a : ι → ℝ) (sign : ι → Bool) (hcont : ∀ i,Continuous (L i)) :
    IsOpen (strictRegion U L a sign) := by
  have h : IsOpen {x | ∀ i,if sign i then L i x<a i else a i<L i x} := by
    rw [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    cases sign i <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact isOpen_lt continuous_const (hcont i)
    · exact isOpen_lt (hcont i) continuous_const
  exact hU.inter h

theorem strictRegion_union {σ ι : Type*}
    (U : Set (σ → ℝ)) (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) :
    (⋃ sign : ι → Bool, strictRegion U L a sign) = U ∩ {x | ∀ i,L i x≠a i} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨sign,hx⟩ := Set.mem_iUnion.mp hx
    refine ⟨hx.1,fun i => ?_⟩
    have hi := hx.2 i
    cases hsign : sign i <;> simp [hsign] at hi <;> linarith
  · intro hx
    refine Set.mem_iUnion.mpr ⟨fun i => decide (L i x<a i),hx.1,?_⟩
    intro i
    by_cases h : L i x<a i
    · simp [h]
    · simp [h]
      exact lt_of_le_of_ne (le_of_not_gt h) (hx.2 i).symm

/-- Boundary points are in a retained chamber closure; no assumption that the
point avoids subdivision hyperplanes is required. -/
theorem retained_chamber_cover {σ ι : Type*} [Fintype σ] [Fintype ι]
    (U : Set (σ → ℝ)) (hU : IsOpen U) (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ)
    (a : ι → ℝ) (hcont : ∀ i,Continuous (L i))
    (hproper : ∀ i,∃ v,L i v≠0) (x : σ → ℝ) (hx : x ∈ U) :
    ∃ sign : ι → Bool, (strictRegion U L a sign).Nonempty ∧
      x ∈ closure (strictRegion U L a sign) := by
  classical
  have hc := (avoid_hyperplanes_dense L a hcont hproper).open_subset_closure_inter hU hx
  rw [← strictRegion_union U L a, closure_iUnion_of_finite] at hc
  obtain ⟨sign,hc⟩ := Set.mem_iUnion.mp hc
  exact ⟨sign,closure_nonempty_iff.mp ⟨x,hc⟩,hc⟩


structure SliceData {σ : Type*} (K : Set (σ → ℝ)) (I : Finset σ)
    (x : σ → ℝ) (r Delta : ℕ) where
  convex : Convex ℝ K
  v0 : σ → ℝ
  v : Fin r → σ → ℝ
  a0 : ℝ
  a : Fin r → ℝ
  nonneg : ∀ i,0 ≤ a i
  sum_one : a0+∑ i,a i=1
  largest : 1 ≤ (r+1:ℝ)*a0
  represents : ∀ j,x j=a0*v0 j+∑ i,a i*v i j
  mem0 : v0 ∈ K
  mem : ∀ i,v i ∈ K
  grid0 : ∀ j ∈ I,∃ z : ℤ,v0 j=(z:ℝ)/Delta
  grid : ∀ i j,j ∈ I → ∃ z : ℤ,v i j=(z:ℝ)/Delta
  int0 : ∀ j,j ∉ I → ∃ z : ℤ,v0 j=z
  fixed : ∀ i j,j ∉ I → v i j=v0 j

def mixedSet {σ κ : Type*} [Fintype σ] (A : κ → σ → ℤ) (b : κ → ℤ)
    (I : Finset σ) : Set (σ → ℝ) :=
  {x | (∀ i,∑ j,(A i j:ℝ)*x j ≤ (b i:ℝ)) ∧ ∀ j,j ∉ I → ∃ z : ℤ,x j=z}

theorem grid_subset_mixed {σ κ : Type*} [Fintype σ] [DecidableEq σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (I : Finset σ) (Q : ℤ) (hQ : Q≠0)
    (x : σ → ℝ) (hx : ScaledPolynomial.gridFeasible A b I Q x) : x ∈ mixedSet A b I := by
  refine ⟨hx.1,?_⟩
  intro j hj
  obtain ⟨z,hz⟩ := (ScaledPolynomial.grid_coordinates I Q hQ x).1 hx.2 j
  exact ⟨z,by simpa [hj] using hz⟩

noncomputable def realPoly {σ : Type*} (f : MvPolynomial σ ℤ) : MvPolynomial σ ℝ :=
  f.map (Int.castRingHom ℝ)
noncomputable def objective {σ : Type*} (f : MvPolynomial σ ℤ) (x : σ → ℝ) : ℝ :=
  f.eval₂ (Int.castRingHom ℝ) x
noncomputable def scaledObjective {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ) (u : σ → ℝ) : ℝ :=
  objective (ScaledPolynomial.scaled f I Q D) u
noncomputable def gridDenom (D r : ℕ) (eps : ℝ) (Delta : ℕ) : ℤ :=
  (gridMultiplier D r eps:ℤ)*Delta

theorem realPoly_eval {σ : Type*} (f : MvPolynomial σ ℤ) (x : σ → ℝ) :
    MvPolynomial.eval x (realPoly f)=objective f x := by
  simp [realPoly, objective, MvPolynomial.eval_map]

theorem realPoly_degree {σ : Type*} (f : MvPolynomial σ ℤ) :
    (realPoly f).totalDegree ≤ f.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)

theorem scaledObjective_identity {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : MvPolynomial σ ℤ) (I : Finset σ) (Q : ℤ) (D : ℕ) (hQ : Q≠0)
    (hdeg : f.totalDegree ≤ D) (u : σ → ℝ) :
    scaledObjective f I Q D u=(Q:ℝ)^D*objective f (ScaledPolynomial.decode I Q u) := by
  exact ScaledPolynomial.eval_scaled f I Q D hQ hdeg u

/-- End-to-end mixed-integer reduction: given published slice/Caratheodory data
and the integer solver's guarantee on the actual scaled polynomial, decode an
answer with the original mixed-integer range-relative guarantee. -/
theorem mixed_integer_reduction {σ κ : Type*} [Fintype σ] [DecidableEq σ] {r : ℕ}
    (A : κ → σ → ℤ) (b : κ → ℤ) (I : Finset σ) (f : MvPolynomial σ ℤ)
    (K : Set (σ → ℝ)) (x : σ → ℝ) (D Delta : ℕ) (fmax eps : ℝ)
    (data : SliceData K I x r Delta) (hKsub : K ⊆ mixedSet A b I)
    (hD : 0<D) (hr : 0<r) (hDelta : 0<Delta) (heps : 0<eps) (heps1 : eps ≤ 1)
    (hx : x ∈ mixedSet A b I) (hdeg : f.totalDegree ≤ D)
    (hb : ∀ z ∈ mixedSet A b I, objective f x ≤ objective f z ∧ objective f z ≤ fmax)
    (hm : SampledMarkov.IntervalMarkovBound D 0 1)
    (umin umax answer : σ → ℝ)
    (humin : ScaledPolynomial.scaledFeasible A b I (gridDenom D r eps Delta) umin)
    (humax : ScaledPolynomial.scaledFeasible A b I (gridDenom D r eps Delta) umax)
    (hanswer : ScaledPolynomial.scaledFeasible A b I (gridDenom D r eps Delta) answer)
    (hmin : ∀ u, ScaledPolynomial.scaledFeasible A b I (gridDenom D r eps Delta) u →
      scaledObjective f I (gridDenom D r eps Delta) D umin ≤
      scaledObjective f I (gridDenom D r eps Delta) D u)
    (hsolver : scaledObjective f I (gridDenom D r eps Delta) D answer-
      scaledObjective f I (gridDenom D r eps Delta) D umin ≤
      (eps/2)*(scaledObjective f I (gridDenom D r eps Delta) D umax-
      scaledObjective f I (gridDenom D r eps Delta) D umin)) :
    let z := ScaledPolynomial.decode I (gridDenom D r eps Delta) answer
    z ∈ mixedSet A b I ∧ 0 ≤ objective f z-objective f x ∧
      objective f z-objective f x ≤ eps*(fmax-objective f x) := by
  let Q := gridDenom D r eps Delta
  have hk := (natural_grid_budget D r eps hD hr heps heps1).1
  have hQ : 0<Q := by dsimp [Q,gridDenom]; positivity
  have hQr : (0:ℝ)<Q := by exact_mod_cast hQ
  have hscale : (0:ℝ)<(Q:ℝ)^D := by positivity
  have hfeas (u) (hu : ScaledPolynomial.scaledFeasible A b I Q u) :
      ScaledPolynomial.decode I Q u ∈ mixedSet A b I :=
    grid_subset_mixed A b I Q (ne_of_gt hQ) _ ((ScaledPolynomial.scaled_feasible_iff A b I Q hQ u).1 hu)
  have hbounds : ∀ z ∈ K,0 ≤ MvPolynomial.eval z (realPoly f)-MvPolynomial.eval x (realPoly f) ∧
      MvPolynomial.eval z (realPoly f)-MvPolynomial.eval x (realPoly f) ≤ fmax-objective f x := by
    intro z hz
    simp only [realPoly_eval]
    have h := hb z (hKsub hz)
    constructor <;> linarith
  obtain ⟨y,hyK,hygrid,hyerr⟩ := mixed_rounding_near K data.convex (realPoly f) I data.v0 data.v
    data.a0 data.a x D Delta (fmax-objective f x) eps hD hr hDelta heps heps1
    data.nonneg data.sum_one data.largest data.represents data.mem0 data.mem data.grid0 data.grid
    data.int0 data.fixed ((realPoly_degree f).trans hdeg) hbounds hm
  simp only [realPoly_eval] at hyerr
  have hyfeas : ScaledPolynomial.gridFeasible A b I Q y := ⟨(hKsub hyK).1,hygrid⟩
  have hmy := hmin (ScaledPolynomial.encode I Q y) ((ScaledPolynomial.grid_feasible_iff A b I Q hQ y).1 hyfeas)
  change scaledObjective f I Q D umin ≤ scaledObjective f I Q D (ScaledPolynomial.encode I Q y) at hmy
  simp only [scaledObjective_identity f I Q D (ne_of_gt hQ) hdeg,
    ScaledPolynomial.decode_encode I Q (ne_of_gt hQ)] at hmy
  have hmy' := (mul_le_mul_iff_right₀ hscale).1 hmy
  change scaledObjective f I Q D answer-scaledObjective f I Q D umin ≤
    (eps/2)*(scaledObjective f I Q D umax-scaledObjective f I Q D umin) at hsolver
  simp only [scaledObjective_identity f I Q D (ne_of_gt hQ) hdeg] at hsolver
  have hsolve : objective f (ScaledPolynomial.decode I Q answer)-objective f (ScaledPolynomial.decode I Q umin) ≤
      (eps/2)*(objective f (ScaledPolynomial.decode I Q umax)-objective f (ScaledPolynomial.decode I Q umin)) := by
    apply (mul_le_mul_iff_right₀ hscale).1
    nlinarith [hsolver]
  have hamin := hb _ (hfeas answer hanswer)
  have hlow := hb _ (hfeas umin humin)
  have hhigh := hb _ (hfeas umax humax)
  have hnear := (le_abs_self _).trans hyerr
  have hrange := mul_le_mul_of_nonneg_left
    (show objective f (ScaledPolynomial.decode I Q umax)-objective f (ScaledPolynomial.decode I Q umin) ≤
      fmax-objective f x by linarith) (show 0 ≤ eps/2 by positivity)
  exact ⟨hfeas answer hanswer,by linarith,by linarith⟩


/-- A sign-consistent nonempty region lies in one generated interval cell,
as does its closure. This includes points on the subdivision hyperplanes. -/
theorem closure_in_interval {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ) (hell : 0<ell)
    (C : Set (σ → ℝ)) (hne : C.Nonempty)
    (hb : ∀ x∈C,∀ i,1/4 ≤ slack A b x i ∧ slack A b x i<2^Phi)
    (hside : ∀ i t, t∈thresholds Phi ell →
      (∀ x∈C,slack A b x i<t) ∨ (∀ x∈C,t<slack A b x i))
    (hcont : ∀ i,Continuous (fun x => slack A b x i)) :
    ∃ c : κ → Interval Phi ell, closure C ⊆ intervalCell A b c := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨c,hc⟩ := interval_cover Phi ell A b x hell (fun i => (hb x hx i).1) (fun i => (hb x hx i).2)
  refine ⟨c,closure_minimal ?_ ?_⟩
  · intro y hy i
    have hlo := hside i (c i).val.1.val (c i).val.1.property
    have hhi := hside i (c i).val.2.val (c i).val.2.property
    constructor
    · rcases hlo with hlo|hlo
      · exact False.elim ((not_lt_of_ge (hc i).1) (hlo x hx))
      · exact (hlo y hy).le
    · rcases hhi with hhi|hhi
      · exact (hhi y hy).le
      · exact False.elim ((not_lt_of_ge (hc i).2) (hhi x hx))
  · unfold intervalCell
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact (isClosed_le continuous_const (hcont i)).inter
      (isClosed_le (hcont i) continuous_const)

/-- Apply the topological chamber-cover theorem to the actual slack-threshold
hyperplanes, and place each retained closure in a generated narrow cell. -/
theorem retained_slack_chamber_cover {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ) (hell : 0<ell)
    (U : Set (σ → ℝ)) (hU : IsOpen U)
    (hb : ∀ x∈U,∀ i,1/4 ≤ slack A b x i ∧ slack A b x i<2^Phi)
    (hcont : ∀ i,Continuous (integerRow (A i)))
    (hproper : ∀ i,∃ v,integerRow (A i) v≠0)
    (x : σ → ℝ) (hx : x∈U) :
    ∃ (sign : (κ × Endpoint Phi ell) → Bool) (c : κ → Interval Phi ell),
      let C := strictRegion U
        (fun p : κ × Endpoint Phi ell => -integerRow (A p.1))
        (fun p => p.2.val-(b p.1:ℝ)-1/2) sign
      C.Nonempty ∧ x∈closure C ∧ closure C ⊆ intervalCell A b c := by
  classical
  let L := fun p : κ × Endpoint Phi ell => -integerRow (A p.1)
  let a := fun p : κ × Endpoint Phi ell => p.2.val-(b p.1:ℝ)-1/2
  have hLc : ∀ p,Continuous (L p) := fun p => (hcont p.1).neg
  have hLp : ∀ p,∃ v,L p v≠0 := by
    intro p
    obtain ⟨v,hv⟩ := hproper p.1
    exact ⟨v,by simpa [L] using hv⟩
  obtain ⟨sign,hne,hxC⟩ := retained_chamber_cover U hU L a hLc hLp x hx
  obtain ⟨c,hc⟩ := closure_in_interval A b Phi ell hell
    (strictRegion U L a sign) hne (fun y hy => hb y hy.1) (by
      intro i t ht
      cases hs : sign (i,⟨t,ht⟩) with
      | false =>
        right
        intro y hy
        have hh := hy.2 (i,⟨t,ht⟩)
        simp [hs,L,a] at hh
        unfold slack
        linarith
      | true =>
        left
        intro y hy
        have hh := hy.2 (i,⟨t,ht⟩)
        simp [hs,L,a] at hh
        unfold slack
        linarith) (fun i => continuous_const.sub (hcont i))
  exact ⟨sign,c,hne,hxC,hc⟩


noncomputable def slackInterior {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi : ℕ) : Set (σ → ℝ) :=
  {x | ∀ i,1/4 < slack A b x i ∧ slack A b x i < 2^Phi}

noncomputable def slackChamber {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool) : Set (σ → ℝ) :=
  strictRegion (slackInterior A b Phi)
    (fun p => -integerRow (A p.1)) (fun p => p.2.val-(b p.1:ℝ)-1/2) sign

theorem slackInterior_open {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi : ℕ)
    (hcont : ∀ i,Continuous (integerRow (A i))) :
    IsOpen (slackInterior A b Phi) := by
  unfold slackInterior
  rw [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  have h : Continuous (fun x => slack A b x i) := continuous_const.sub (hcont i)
  exact (isOpen_lt continuous_const h).inter (isOpen_lt h continuous_const)

theorem slack_chamber_narrow {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ) (hell : 0<ell)
    (hcont : ∀ i,Continuous (integerRow (A i)))
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hne : (slackChamber A b Phi ell sign).Nonempty) :
    ∃ c : κ → Interval Phi ell, closure (slackChamber A b Phi ell sign) ⊆ intervalCell A b c := by
  apply closure_in_interval A b Phi ell hell _ hne
  · intro x hx i
    exact ⟨(hx.1 i).1.le,(hx.1 i).2⟩
  · intro i t ht
    cases hs : sign (i,⟨t,ht⟩) with
    | false =>
      right
      intro y hy
      have hh := hy.2 (i,⟨t,ht⟩)
      simp [hs] at hh
      unfold slack
      linarith
    | true =>
      left
      intro y hy
      have hh := hy.2 (i,⟨t,ht⟩)
      simp [hs] at hh
      unfold slack
      linarith
  · exact fun i => continuous_const.sub (hcont i)

/-- The approximation guarantee for the actual retained slack-chamber closures.
Proper rows (zero rows are removed in preprocessing), complete feasible candidates,
objective extrema, and Markov remain explicit inputs; coverage and widths do not. -/
theorem chamber_approximation {σ κ : Type*} [Fintype σ] [Fintype κ]
    (f : MvPolynomial σ ℝ) (A : κ → σ → ℤ) (b : κ → ℤ)
    (Y : Finset (σ → ℝ)) (x : σ → ℝ) (fmax eps : ℝ) (D Phi : ℕ)
    (hD : 0<D) (heps : 0<eps) (hdeg : f.totalDegree ≤ D)
    (hx : x ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ)
    (hbounds : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
      MvPolynomial.eval x f ≤ MvPolynomial.eval z f ∧ MvPolynomial.eval z f ≤ fmax)
    (hupper : ∀ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
      ∀ i, slack A b z i < (2:ℝ)^Phi)
    (hcont : ∀ i,Continuous (integerRow (A i)))
    (hproper : ∀ i,∃ v,integerRow (A i) v≠0)
    (hfeasible : ∀ y ∈ Y, y ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ)
    (hcomplete : ∀ sign : (κ × Endpoint Phi (max (D^2) ⌈(D:ℝ)/Real.sqrt eps⌉₊)) → Bool,
      (∃ z ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ,
        z ∈ closure (slackChamber A b Phi _ sign)) →
      ∃ y ∈ Y, y ∈ closure (slackChamber A b Phi _ sign))
    (hmarkov : SampledMarkov.MarkovBound D (max (D^2) ⌈(D:ℝ)/Real.sqrt eps⌉₊)) :
    ∃ best ∈ Y, best ∈ linearIntegerSet (fun i => integerRow (A i)) (fun i => (b i:ℝ)) Set.univ ∧
      (∀ y ∈ Y, MvPolynomial.eval best f ≤ MvPolynomial.eval y f) ∧
      0 ≤ MvPolynomial.eval best f-MvPolynomial.eval x f ∧
      MvPolynomial.eval best f-MvPolynomial.eval x f ≤ eps*(fmax-MvPolynomial.eval x f) := by
  classical
  have hell := (FPTASCalculations.ceiling_refinement hD heps).1
  apply shifted_slack_cover_guarantee f A b (fun sign => closure (slackChamber A b Phi _ sign)) Y x fmax eps D
    hD heps hdeg hx hbounds ?_ hfeasible hcomplete hmarkov ?_
  · intro z hz
    have hzU : z∈slackInterior A b Phi := by
      intro i
      have hp := shifted_slack_positive A b z hz.1 i
      refine ⟨?_,hupper z hz i⟩
      dsimp [slack]
      linarith
    obtain ⟨sign,c,hne,hzC,hc⟩ := retained_slack_chamber_cover A b Phi _ hell
      (slackInterior A b Phi) (slackInterior_open A b Phi hcont)
      (fun y hy i => ⟨(hy i).1.le,(hy i).2⟩) hcont hproper z hzU
    exact ⟨sign,hzC⟩
  · intro sign u hu v hv
    have hne := closure_nonempty_iff.mp ⟨u,hu⟩
    obtain ⟨c,hc⟩ := slack_chamber_narrow A b Phi _ hell hcont sign hne
    simpa only [slack,Nat.cast_max,Nat.cast_pow] using interval_widths A b c u v (hc hu) (hc hv)


/-- Closing a nonempty strict finite linear system changes precisely < to ≤.
The nonempty hypothesis is essential. -/
theorem closure_strict_linear {σ ι : Type*} [Fintype σ]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (hc : ∀ i,Continuous (L i))
    (hne : ({x | ∀ i,L i x<a i} : Set (σ → ℝ)).Nonempty) :
    closure {x | ∀ i,L i x<a i} = {x | ∀ i,L i x≤a i} := by
  apply Set.Subset.antisymm
  · refine closure_minimal (t := {x | ∀ i,L i x≤a i}) (fun x hx i => (hx i).le) ?_
    rw [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_le (hc i) continuous_const)
  · intro y hy
    obtain ⟨x,hx⟩ := hne
    have hseg : openSegment ℝ x y ⊆ {z | ∀ i,L i z<a i} := by
      intro z hz i
      obtain ⟨u,v,hu,hv,hs,rfl⟩ := hz
      simp only [map_add,map_smul,smul_eq_mul]
      have h1 := mul_lt_mul_of_pos_left (hx i) hu
      have h2 := mul_le_mul_of_nonneg_left (hy i) hv.le
      have hs' := congrArg (fun t : ℝ => t*a i) hs
      nlinarith
    exact closure_mono hseg (segment_subset_closure_openSegment (right_mem_segment ℝ x y))

theorem threshold_rational (ell k j : ℕ) :
    ∃ q : ℚ,(q:ℝ)=threshold ell k j := by
  refine ⟨(2:ℚ)^k/4*(1+(j:ℚ)/ell),?_⟩
  simp [threshold]

theorem endpoint_rational (Phi ell : ℕ) (t : Endpoint Phi ell) :
    ∃ q : ℚ,(q:ℝ)=t.val := by
  classical
  have ht := t.property
  unfold thresholds at ht
  rcases Finset.mem_insert.mp ht with ht|ht
  · exact ⟨(2:ℚ)^Phi,by simpa using ht.symm⟩
  · obtain ⟨p,hp,hp'⟩ := Finset.mem_image.mp ht
    obtain ⟨q,hq⟩ := threshold_rational ell p.1 p.2
    exact ⟨q,hq.trans hp'⟩

noncomputable def endpointRat {Phi ell : ℕ} (t : Endpoint Phi ell) : ℚ :=
  (endpoint_rational Phi ell t).choose

theorem endpointRat_cast {Phi ell : ℕ} (t : Endpoint Phi ell) :
    (endpointRat t:ℝ)=t.val := (endpoint_rational Phi ell t).choose_spec

abbrev ChamberRow (κ : Type*) (Phi ell : ℕ) := (κ × Bool) ⊕ (κ × Endpoint Phi ell)

noncomputable def chamberMatrix {σ κ : Type*} (A : κ → σ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) : ChamberRow κ Phi ell → σ → ℚ
  | .inl (i,upper),j => if upper then -(A i j:ℚ) else (A i j:ℚ)
  | .inr (i,t),j => if sign (i,t) then -(A i j:ℚ) else (A i j:ℚ)

noncomputable def chamberRhs {κ : Type*} (b : κ → ℤ)
    {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool) : ChamberRow κ Phi ell → ℚ
  | .inl (i,upper) => if upper then (2:ℚ)^Phi-(b i:ℚ)-1/2 else (b i:ℚ)+1/4
  | .inr (i,t) => if sign (i,t) then endpointRat t-(b i:ℚ)-1/2 else (b i:ℚ)+1/2-endpointRat t

noncomputable def rationalRow {σ : Type*} [Fintype σ] (a : σ → ℚ) : (σ → ℝ) →ₗ[ℝ] ℝ :=
  ∑ j, (a j:ℝ) • LinearMap.proj j

theorem rationalRow_continuous {σ : Type*} [Fintype σ] (a : σ → ℚ) :
    Continuous (rationalRow a) := by
  have he : (rationalRow a : (σ → ℝ) → ℝ) = (fun x => ∑ j,(a j:ℝ)*x j) := by
    ext x
    simp [rationalRow]
  rw [he]
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_apply j))

theorem chamber_strict_description {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool) :
    slackChamber A b Phi ell sign =
      {x | ∀ r, rationalRow (chamberMatrix A sign r) x < (chamberRhs b sign r:ℝ)} := by
  ext x
  simp only [slackChamber,strictRegion,slackInterior,Set.mem_setOf_eq]
  constructor
  · intro hx r
    cases r with
    | inl p =>
      obtain ⟨i,u⟩ := p
      have hi := hx.1 i
      cases u <;> simp [chamberMatrix,chamberRhs,rationalRow,integerRow,slack] at * <;> linarith
    | inr p =>
      obtain ⟨i,t⟩ := p
      have hi := hx.2 (i,t)
      cases hs : sign (i,t) <;> simp [hs,chamberMatrix,chamberRhs,rationalRow,integerRow,endpointRat_cast] at * <;> linarith
  · intro hx
    constructor
    · intro i
      have h1 := hx (.inl (i,false))
      have h2 := hx (.inl (i,true))
      simp [chamberMatrix,chamberRhs,rationalRow,integerRow,slack] at *
      constructor <;> linarith
    · intro p
      obtain ⟨i,t⟩ := p
      have hi := hx (.inr (i,t))
      cases hs : sign (i,t) <;> simp [hs,chamberMatrix,chamberRhs,rationalRow,integerRow,endpointRat_cast] at * <;> linarith

/-- Explicit rational matrix and right-hand side for each retained closure. -/
theorem chamber_closure_rational_description {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hne : (slackChamber A b Phi ell sign).Nonempty) :
    closure (slackChamber A b Phi ell sign) =
      {x | ∀ r,rationalRow (chamberMatrix A sign r) x ≤ (chamberRhs b sign r:ℝ)} := by
  rw [chamber_strict_description] at hne ⊢
  exact closure_strict_linear _ _ (fun r => rationalRow_continuous _) hne


noncomputable def lowerSlacks {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : Finset ℚ := by
  classical
  exact insert (1/4) ((Finset.univ.filter (fun t => sign (i,t)=false)).image endpointRat)

noncomputable def upperSlacks {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : Finset ℚ := by
  classical
  exact insert ((2:ℚ)^Phi) ((Finset.univ.filter (fun t => sign (i,t)=true)).image endpointRat)

theorem lowerSlacks_nonempty {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : (lowerSlacks sign i).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

theorem upperSlacks_nonempty {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : (upperSlacks sign i).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

noncomputable def lowerSlack {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : ℚ :=
  (lowerSlacks sign i).max' (lowerSlacks_nonempty sign i)
noncomputable def upperSlack {κ : Type*} {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (i : κ) : ℚ :=
  (upperSlacks sign i).min' (upperSlacks_nonempty sign i)

theorem rational_max_le (S : Finset ℚ) (hS : S.Nonempty) (x : ℝ) :
    ((S.max' hS:ℚ):ℝ) ≤ x ↔ ∀ q∈S,(q:ℝ)≤x := by
  constructor
  · intro h q hq
    have hq' : (q:ℝ) ≤ (S.max' hS:ℝ) := by exact_mod_cast S.le_max' q hq
    exact hq'.trans h
  · intro h
    exact h _ (S.max'_mem hS)

theorem le_rational_min (S : Finset ℚ) (hS : S.Nonempty) (x : ℝ) :
    x ≤ ((S.min' hS:ℚ):ℝ) ↔ ∀ q∈S,x≤(q:ℝ) := by
  constructor
  · intro h q hq
    exact h.trans (by exact_mod_cast S.min'_le q hq)
  · intro h
    exact h _ (S.min'_mem hS)

/-- All threshold halfspaces in a row compress to a maximum lower bound and a
minimum upper bound, both rational. -/
theorem compressed_slack_description {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool) (x : σ → ℝ) :
    (∀ r,rationalRow (chamberMatrix A sign r) x ≤ (chamberRhs b sign r:ℝ)) ↔
      ∀ i,(lowerSlack sign i:ℝ) ≤ slack A b x i ∧ slack A b x i ≤ (upperSlack sign i:ℝ) := by
  classical
  have row (i : κ) :
      ((lowerSlack sign i:ℝ) ≤ slack A b x i ∧ slack A b x i ≤ (upperSlack sign i:ℝ)) ↔
      (1/4 ≤ slack A b x i ∧ slack A b x i ≤ 2^Phi) ∧
      (∀ t : Endpoint Phi ell,if sign (i,t) then slack A b x i ≤ t.val else t.val ≤ slack A b x i) := by
    simp only [lowerSlack,upperSlack,rational_max_le,le_rational_min,
      lowerSlacks,upperSlacks,Finset.mem_insert,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h
      refine ⟨⟨?_,?_⟩,?_⟩
      · simpa using h.1 (1/4) (Or.inl rfl)
      · simpa using h.2 ((2:ℚ)^Phi) (Or.inl rfl)
      · intro t
        cases hs : sign (i,t)
        · simpa [hs,endpointRat_cast] using h.1 (endpointRat t) (Or.inr ⟨t,hs,rfl⟩)
        · simpa [hs,endpointRat_cast] using h.2 (endpointRat t) (Or.inr ⟨t,hs,rfl⟩)
    · intro h
      constructor
      · intro q hq
        rcases hq with rfl|⟨t,ht,rfl⟩
        · simpa using h.1.1
        · simpa [ht,endpointRat_cast] using h.2 t
      · intro q hq
        rcases hq with rfl|⟨t,ht,rfl⟩
        · simpa using h.1.2
        · simpa [ht,endpointRat_cast] using h.2 t
  constructor
  · intro h i
    apply (row i).2
    have h1 := h (.inl (i,false))
    have h2 := h (.inl (i,true))
    constructor
    · simp [chamberMatrix,chamberRhs,rationalRow,integerRow,slack] at *
      constructor <;> linarith
    · intro t
      have ht := h (.inr (i,t))
      cases hs : sign (i,t) <;> simp [hs,chamberMatrix,chamberRhs,rationalRow,integerRow,slack,endpointRat_cast] at * <;> linarith
  · intro h r
    cases r with
    | inl p =>
      obtain ⟨i,u⟩ := p
      have hi := ((row i).1 (h i)).1
      cases u <;> simp [chamberMatrix,chamberRhs,rationalRow,integerRow,slack] at * <;> linarith
    | inr p =>
      obtain ⟨i,t⟩ := p
      have hi := ((row i).1 (h i)).2 t
      cases hs : sign (i,t) <;> simp [hs,chamberMatrix,chamberRhs,rationalRow,integerRow,slack,endpointRat_cast] at * <;> linarith

theorem chamber_closure_compressed {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hne : (slackChamber A b Phi ell sign).Nonempty) :
    closure (slackChamber A b Phi ell sign) =
      {x | ∀ i,(lowerSlack sign i:ℝ) ≤ slack A b x i ∧ slack A b x i ≤ (upperSlack sign i:ℝ)} := by
  rw [chamber_closure_rational_description A b Phi ell sign hne]
  ext x
  exact compressed_slack_description A b Phi ell sign x


/-- The compressed closure description yields exactly the rounded integer
slack tests used by the feasibility oracle. -/
theorem chamber_integer_tests {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hne : (slackChamber A b Phi ell sign).Nonempty) (z : σ → ℤ) :
    (fun j => (z j:ℝ)) ∈ closure (slackChamber A b Phi ell sign) ↔
      ∀ i, ⌈(lowerSlack sign i:ℝ)-1/2⌉ ≤ b i-∑ j,A i j*z j ∧
        b i-∑ j,A i j*z j ≤ ⌊(upperSlack sign i:ℝ)-1/2⌋ := by
  rw [chamber_closure_compressed A b Phi ell sign hne]
  change (∀ i, _ ∧ _) ↔ _
  apply forall_congr'
  intro i
  have he : slack A b (fun j => (z j:ℝ)) i = ((b i-∑ j,A i j*z j:ℤ):ℝ)+1/2 := by
    simp [slack,integerRow]
    ring
  rw [he]
  exact ScaledPolynomial.shifted_integer_slack_interval _ _ _


/-- For finitely many proper linear inequalities, the interior is obtained
by making every inequality strict. Zero rows must first be removed. -/
theorem interior_linear_system {σ ι : Type*} [Fintype σ] [Fintype ι]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (hc : ∀ i,Continuous (L i)) (hp : ∀ i,∃ v,L i v≠0) :
    interior {x | ∀ i,L i x≤a i} = {x | ∀ i,L i x<a i} := by
  apply Set.Subset.antisymm
  · intro x hx i
    have hi : x ∈ interior ((L i) ⁻¹' Set.Iic (a i)) :=
      interior_mono (show {y | ∀ j,L j y≤a j} ⊆ (L i) ⁻¹' Set.Iic (a i) from fun y hy => hy i) hx
    obtain ⟨v,hv⟩ := hp i
    have hs : Function.Surjective (L i) := by
      intro t
      refine ⟨(t/L i v) • v,?_⟩
      simp [map_smul,hv]
    have ho := IsModuleTopology.isOpenMap_of_surjective hs
    have ht := ho.interior_preimage_subset_preimage_interior hi
    simpa using ht
  · have ho : IsOpen {x | ∀ i,L i x<a i} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt (hc i) continuous_const)
    intro x hx
    apply interior_mono (show {x | ∀ i,L i x<a i} ⊆ {x | ∀ i,L i x≤a i} from
      fun y hy i => (hy i).le)
    rwa [ho.interior_eq]

noncomputable def marginFeasible {σ ι : Type*}
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) (x : σ → ℝ) (delta : ℝ) : Prop :=
  0≤delta ∧ delta≤1 ∧ ∀ i,L i x+delta≤a i

/-- A finite strict system has a common positive slack, capped at one.
This also handles an empty list of constraints. -/
theorem strict_iff_positive_margin {σ ι : Type*} [Fintype ι]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) (x : σ → ℝ) :
    (∀ i,L i x<a i) ↔ ∃ delta,0<delta ∧ marginFeasible L a x delta := by
  classical
  constructor
  · intro hx
    let S : Finset ℝ := insert 1 (Finset.univ.image (fun i => a i-L i x))
    have hS : S.Nonempty := Finset.insert_nonempty _ _
    let delta := S.min' hS
    have hpos : 0<delta := by
      have hmem := S.min'_mem hS
      rcases Finset.mem_insert.mp hmem with h|h
      · change 0<S.min' hS
        rw [h]
        norm_num
      · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
        change 0<S.min' hS
        rw [← he]
        exact sub_pos.mpr (hx i)
    refine ⟨delta,hpos,hpos.le,?_,?_⟩
    · exact S.min'_le 1 (Finset.mem_insert_self _ _)
    · intro i
      have hi : delta ≤ a i-L i x := S.min'_le _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))
      linarith
  · rintro ⟨delta,hd,_,_,h⟩ i
    linarith [h i]

theorem margin_feasible_iff {σ ι : Type*}
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) :
    (∃ x delta,marginFeasible L a x delta) ↔ ({x | ∀ i,L i x≤a i} : Set (σ → ℝ)).Nonempty := by
  constructor
  · rintro ⟨x,delta,hd,_,h⟩
    exact ⟨x,fun i => by linarith [h i]⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,0,le_rfl,by norm_num,by simpa using hx⟩

theorem interior_iff_positive_margin {σ ι : Type*} [Fintype σ] [Fintype ι]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (hc : ∀ i,Continuous (L i)) (hp : ∀ i,∃ v,L i v≠0) :
    (interior {x | ∀ i,L i x≤a i}).Nonempty ↔
      ∃ x delta,0<delta ∧ marginFeasible L a x delta := by
  rw [interior_linear_system L a hc hp]
  exact exists_congr (fun x => strict_iff_positive_margin L a x)

/-- Once an LP solver returns a feasible optimum, its sign exactly decides
nonempty interior. No implementation or operation count is assumed proved. -/
theorem margin_optimum_test {σ ι : Type*} [Fintype σ] [Fintype ι]
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (hc : ∀ i,Continuous (L i)) (hp : ∀ i,∃ v,L i v≠0)
    (xstar : σ → ℝ) (dstar : ℝ) (hf : marginFeasible L a xstar dstar)
    (hopt : ∀ x delta,marginFeasible L a x delta → delta≤dstar) :
    0<dstar ↔ (interior {x | ∀ i,L i x≤a i}).Nonempty := by
  rw [interior_iff_positive_margin L a hc hp]
  constructor
  · intro h
    exact ⟨xstar,dstar,h,hf⟩
  · rintro ⟨x,delta,hd,h⟩
    exact hd.trans_le (hopt x delta h)

/-- Every normal in the rational chamber system is proper if the original
rows are proper; signs and outer bounds do not introduce a zero normal. -/
theorem chamber_rows_proper {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) {Phi ell : ℕ} (sign : (κ × Endpoint Phi ell) → Bool)
    (hp : ∀ i,∃ v,integerRow (A i) v≠0) :
    ∀ r,∃ v,rationalRow (chamberMatrix A sign r) v≠0 := by
  intro r
  cases r with
  | inl p =>
    obtain ⟨i,u⟩ := p
    obtain ⟨v,hv⟩ := hp i
    refine ⟨v,?_⟩
    cases u <;> simpa [chamberMatrix,rationalRow,integerRow] using hv
  | inr p =>
    obtain ⟨i,t⟩ := p
    obtain ⟨v,hv⟩ := hp i
    refine ⟨v,?_⟩
    cases hs : sign (i,t) <;> simpa [hs,chamberMatrix,rationalRow,integerRow] using hv

/-- Exact retention test for the actual rational candidate chamber system,
including candidates whose strict sign region is empty. -/
theorem chamber_margin_test {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hp : ∀ i,∃ v,integerRow (A i) v≠0) :
    (interior {x | ∀ r,rationalRow (chamberMatrix A sign r) x ≤ (chamberRhs b sign r:ℝ)}).Nonempty ↔
      (slackChamber A b Phi ell sign).Nonempty := by
  classical
  rw [interior_linear_system _ _ (fun r => rationalRow_continuous _) (chamber_rows_proper A sign hp)]
  rw [chamber_strict_description A b Phi ell sign]

/-- The algorithm may retain precisely those sign regions whose rational
common-margin LP has a positive optimum. -/
theorem chamber_optimum_test {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hp : ∀ i,∃ v,integerRow (A i) v≠0)
    (xstar : σ → ℝ) (dstar : ℝ)
    (hf : marginFeasible (fun r => rationalRow (chamberMatrix A sign r))
      (fun r => (chamberRhs b sign r:ℝ)) xstar dstar)
    (hopt : ∀ x delta,marginFeasible (fun r => rationalRow (chamberMatrix A sign r))
      (fun r => (chamberRhs b sign r:ℝ)) x delta → delta≤dstar) :
    0<dstar ↔ (slackChamber A b Phi ell sign).Nonempty := by
  classical
  rw [← chamber_margin_test A b Phi ell sign hp]
  exact margin_optimum_test _ _ (fun r => rationalRow_continuous _) (chamber_rows_proper A sign hp) xstar dstar hf hopt


noncomputable def compressedRhs {κ : Type*} (b : κ → ℤ) {Phi ell : ℕ}
    (sign : (κ × Endpoint Phi ell) → Bool) (p : κ × Bool) : ℚ :=
  if p.2 then upperSlack sign p.1-(b p.1:ℚ)-1/2
  else (b p.1:ℚ)+1/2-lowerSlack sign p.1

theorem compressed_linear_description {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool) :
    {x | ∀ p : κ × Bool,rationalRow (chamberMatrix A sign (.inl p)) x ≤ (compressedRhs b sign p:ℝ)} =
      {x | ∀ r,rationalRow (chamberMatrix A sign r) x ≤ (chamberRhs b sign r:ℝ)} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [compressed_slack_description A b Phi ell sign x]
  constructor
  · intro h i
    have h1 := h (i,false)
    have h2 := h (i,true)
    simp [chamberMatrix,rationalRow,compressedRhs,integerRow,slack] at *
    constructor <;> linarith
  · intro h p
    obtain ⟨i,u⟩ := p
    have hi := h i
    cases u <;> simp [chamberMatrix,rationalRow,compressedRhs,integerRow,slack] at * <;> linarith

/-- The same exact test applies to the algorithm's compressed 2m-row LP. -/
theorem compressed_optimum_test {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ)
    (sign : (κ × Endpoint Phi ell) → Bool)
    (hp : ∀ i,∃ v,integerRow (A i) v≠0)
    (xstar : σ → ℝ) (dstar : ℝ)
    (hf : marginFeasible (fun p : κ × Bool => rationalRow (chamberMatrix A sign (.inl p)))
      (fun p => (compressedRhs b sign p:ℝ)) xstar dstar)
    (hopt : ∀ x delta,marginFeasible (fun p : κ × Bool => rationalRow (chamberMatrix A sign (.inl p)))
      (fun p => (compressedRhs b sign p:ℝ)) x delta → delta≤dstar) :
    0<dstar ↔ (slackChamber A b Phi ell sign).Nonempty := by
  have h := margin_optimum_test _ _ (fun p => rationalRow_continuous _)
    (fun p => chamber_rows_proper A sign hp (.inl p)) xstar dstar hf hopt
  rw [compressed_linear_description A b Phi ell sign] at h
  exact h.trans (chamber_margin_test A b Phi ell sign hp)

end CoverAssembly
