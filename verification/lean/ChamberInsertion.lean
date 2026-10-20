import CoverAssembly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace ChamberInsertion
open CoverArithmetic

noncomputable def patterns {E ι : Type*} [Fintype ι]
    (U : Set E) (L : ι → E → ℝ) (a : ι → ℝ) : Finset (ι → Bool) := by
  classical
  exact Finset.univ.filter (fun s => ∃ x∈U,∀ i,if s i then L i x<a i else a i<L i x)

theorem mem_patterns {E ι : Type*} [Fintype ι]
    (U : Set E) (L : ι → E → ℝ) (a : ι → ℝ) (s : ι → Bool) :
    s∈patterns U L a ↔ ∃ x∈U,∀ i,if s i then L i x<a i else a i<L i x := by
  classical
  simp [patterns]

theorem patterns_mono {E ι : Type*} [Fintype ι]
    (U V : Set E) (L : ι → E → ℝ) (a : ι → ℝ) (h : U⊆V) :
    patterns U L a ⊆ patterns V L a := by
  intro s hs
  rw [mem_patterns] at hs ⊢
  obtain ⟨x,hx,hp⟩ := hs
  exact ⟨x,h hx,hp⟩

theorem sign_cell_convex {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (U : Set E) (hU : Convex ℝ U) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ) (s : ι → Bool) :
    Convex ℝ {x | x∈U ∧ ∀ i,if s i then L i x<a i else a i<L i x} := by
  intro x hx y hy u v hu hv huv
  refine ⟨hU hx.1 hy.1 hu hv huv,?_⟩
  intro i
  have hxi := hx.2 i
  have hyi := hy.2 i
  have he := congrArg (fun t : ℝ => t*a i) huv
  simp only [map_add,map_smul,smul_eq_mul]
  cases hs : s i <;> simp [hs] at hxi hyi ⊢
  · by_cases hu0 : u=0
    · subst u; simp at huv; subst v; simpa using hyi
    · have h1 := mul_lt_mul_of_pos_left hxi (lt_of_le_of_ne hu (Ne.symm hu0))
      have h2 := mul_le_mul_of_nonneg_left hyi.le hv
      nlinarith
  · by_cases hu0 : u=0
    · subst u; simp at huv; subst v; simpa using hyi
    · have h1 := mul_lt_mul_of_pos_left hxi (lt_of_le_of_ne hu (Ne.symm hu0))
      have h2 := mul_le_mul_of_nonneg_left hyi.le hv
      nlinarith

/-- A chamber meeting both sides meets the inserted hyperplane, with exactly
the same old strict signs. Convexity is the essential geometric input. -/
theorem crossing_witness {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : Set E) (hC : Convex ℝ C) (g : E →ₗ[ℝ] ℝ) (b : ℝ)
    (x y : E) (hx : x∈C) (hy : y∈C) (hlo : g x<b) (hhi : b<g y) :
    ∃ z∈C,g z=b := by
  let t := (b-g x)/(g y-g x)
  have hd : 0<g y-g x := by linarith
  have ht : 0<t := div_pos (by linarith) hd
  have ht1 : t<1 := (div_lt_one hd).2 (by linarith)
  refine ⟨(1-t) • x+t • y,hC hx hy (by linarith) ht.le (by ring),?_⟩
  simp only [map_add,map_smul,smul_eq_mul]
  dsimp [t]
  field_simp
  <;> ring

/-- Identity on old sign vectors is the injection from split chambers to
regions of the induced arrangement. -/
theorem split_patterns_subset_section {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (U : Set E) (hU : Convex ℝ U) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (g : E →ₗ[ℝ] ℝ) (b : ℝ) :
    patterns (U∩{x|g x<b}) (fun i => L i) a ∩ patterns (U∩{x|b<g x}) (fun i => L i) a ⊆
      patterns (U∩{x|g x=b}) (fun i => L i) a := by
  classical
  intro s hs
  obtain ⟨hl,hh⟩ := Finset.mem_inter.mp hs
  rw [mem_patterns] at hl hh ⊢
  obtain ⟨x,hx,hxs⟩ := hl
  obtain ⟨y,hy,hys⟩ := hh
  obtain ⟨z,hz,hgz⟩ := crossing_witness _ (sign_cell_convex U hU L a s) g b x y
    ⟨hx.1,hxs⟩ ⟨hy.1,hys⟩ hx.2 hy.2
  exact ⟨z,⟨hz.1,hgz⟩,hz.2⟩

/-- The actual geometric insertion inequality, without an assumed recurrence. -/
theorem insertion_inequality {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (U : Set E) (hU : Convex ℝ U) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (g : E →ₗ[ℝ] ℝ) (b : ℝ) :
    (patterns (U∩{x|g x<b}) (fun i => L i) a).card+
      (patterns (U∩{x|b<g x}) (fun i => L i) a).card ≤
    (patterns U (fun i => L i) a).card+(patterns (U∩{x|g x=b}) (fun i => L i) a).card := by
  classical
  rw [← Finset.card_union_add_card_inter]
  apply Nat.add_le_add
  · apply Finset.card_le_card
    exact Finset.union_subset (patterns_mono _ _ _ _ Set.inter_subset_left)
      (patterns_mono _ _ _ _ Set.inter_subset_left)
  · exact Finset.card_le_card (split_patterns_subset_section U hU L a g b)


theorem patterns_cons {E : Type*} {H : ℕ} (U : Set E)
    (L : Fin (H+1) → E → ℝ) (a : Fin (H+1) → ℝ) (b : Bool) (s : Fin H → Bool) :
    Fin.cons b s ∈ patterns U L a ↔
      s∈patterns (U∩{x|if b then L 0 x<a 0 else a 0<L 0 x})
        (fun i : Fin H => L i.succ) (fun i : Fin H => a i.succ) := by
  rw [mem_patterns,mem_patterns]
  simp only [Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ]
  constructor
  · rintro ⟨x,hx,h0,hs⟩; exact ⟨x,⟨hx,h0⟩,hs⟩
  · rintro ⟨x,⟨hx,h0⟩,hs⟩; exact ⟨x,hx,h0,hs⟩

theorem patterns_head_card {E : Type*} {H : ℕ} (U : Set E)
    (L : Fin (H+1) → E → ℝ) (a : Fin (H+1) → ℝ) (b : Bool) :
    ((patterns U L a).filter (fun s => s 0=b)).card =
      (patterns (U∩{x|if b then L 0 x<a 0 else a 0<L 0 x})
        (fun i : Fin H => L i.succ) (fun i : Fin H => a i.succ)).card := by
  classical
  symm
  apply Finset.card_bij (fun (s : Fin H → Bool) _ => (Fin.cons b s : Fin (H+1) → Bool))
  · intro s hs
    exact Finset.mem_filter.mpr ⟨(patterns_cons U L a b s).2 hs,by simp⟩
  · intro s hs t ht he
    ext i
    exact congrFun he i.succ
  · intro s hs
    obtain ⟨hmem,h0⟩ := Finset.mem_filter.mp hs
    have he : Fin.cons b (fun i => s i.succ)=s := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using h0.symm
      · simp
    refine ⟨fun i => s i.succ,?_,he⟩
    apply (patterns_cons U L a b _).1
    rwa [he]

theorem patterns_succ_card {E : Type*} {H : ℕ} (U : Set E)
    (L : Fin (H+1) → E → ℝ) (a : Fin (H+1) → ℝ) :
    (patterns U L a).card =
      (patterns (U∩{x|L 0 x<a 0}) (fun i : Fin H => L i.succ) (fun i : Fin H => a i.succ)).card+
      (patterns (U∩{x|a 0<L 0 x}) (fun i : Fin H => L i.succ) (fun i : Fin H => a i.succ)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s:=patterns U L a) (p:=fun s => s 0=true)
  have hn : (fun s : Fin (H+1) → Bool => ¬s 0=true) = (fun s => s 0=false) := by
    funext s
    simp
  simp only [hn] at h
  rw [patterns_head_card,patterns_head_card] at h
  simpa using h.symm

/-- Restricting to the inserted affine hyperplane gives linear forms on its
kernel, after translating by any point of that hyperplane. -/
theorem section_patterns {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (U : Set E) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (g : E →ₗ[ℝ] ℝ) (b : ℝ) (p : E) (hp : g p=b) :
    patterns (U∩{x|g x=b}) (fun i => L i) a =
      patterns {v : g.ker | p+(v:E)∈U}
        (fun i => L i ∘ₗ g.ker.subtype) (fun i => a i-L i p) := by
  classical
  ext s
  rw [mem_patterns,mem_patterns]
  constructor
  · rintro ⟨x,hx,hs⟩
    have hxg : g x=b := hx.2
    have hk : x-p∈g.ker := by simp [LinearMap.mem_ker,map_sub,hxg,hp]
    refine ⟨⟨x-p,hk⟩,?_,?_⟩
    · simpa using hx.1
    · intro i
      have hi := hs i
      cases hsi : s i <;> simp [hsi,LinearMap.comp_apply,map_sub] at * <;> linarith
  · rintro ⟨v,hv,hs⟩
    refine ⟨p+(v:E),⟨hv,?_⟩,?_⟩
    · simp [map_add,hp,show g (v:E)=0 from v.property]
    · intro i
      have hi := hs i
      cases hsi : s i <;> simp [hsi,LinearMap.comp_apply,map_add] at * <;> linarith

theorem section_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (U : Set E) (hU : Convex ℝ U) (g : E →ₗ[ℝ] ℝ) (p : E) :
    Convex ℝ {v : g.ker | p+(v:E)∈U} := by
  intro u hu v hv a b ha hb hab
  have hh := hU hu hv ha hb hab
  have he : p+((a • u+b • v : g.ker):E) = a • (p+(u:E))+b • (p+(v:E)) := by
    simp only [Submodule.coe_add,Submodule.coe_smul,smul_add]
    have hpp : a • p+b • p=p := by rw [← add_smul,hab,one_smul]
    calc
      p+(a • (u:E)+b • (v:E)) = (a • p+b • p)+(a • (u:E)+b • (v:E)) := by rw [hpp]
      _ = _ := by abel
  change p+((a • u+b • v : g.ker):E)∈U
  rw [he]
  exact hh

theorem kernel_dimension {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (g : E →ₗ[ℝ] ℝ) (hg : ∃ v,g v≠0) :
    Module.finrank ℝ E = Module.finrank ℝ g.ker+1 := by
  obtain ⟨v,hv⟩ := hg
  have hs : Function.Surjective g := by
    intro t
    refine ⟨(t/g v) • v,?_⟩
    simp [map_smul,hv]
  have h := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at h
  simpa [add_comm] using h.symm


theorem zero_insertion {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (U : Set E) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ)
    (g : E →ₗ[ℝ] ℝ) (b : ℝ) (hg : g=0) :
    (patterns (U∩{x|g x<b}) (fun i => L i) a).card+
      (patterns (U∩{x|b<g x}) (fun i => L i) a).card ≤
    (patterns U (fun i => L i) a).card := by
  classical
  have hd : Disjoint (patterns (U∩{x|g x<b}) (fun i => L i) a)
      (patterns (U∩{x|b<g x}) (fun i => L i) a) := by
    apply Finset.disjoint_left.mpr
    intro s hl hh
    rw [mem_patterns] at hl hh
    obtain ⟨x,hx,_⟩ := hl
    obtain ⟨y,hy,_⟩ := hh
    have hx' : g x<b := hx.2
    have hy' : b<g y := hy.2
    simp [hg] at hx' hy'
    linarith
  rw [← Finset.card_union_of_disjoint hd]
  apply Finset.card_le_card
  exact Finset.union_subset (patterns_mono _ _ _ _ Set.inter_subset_left)
    (patterns_mono _ _ _ _ Set.inter_subset_left)

theorem bound_mono_hyperplanes (H d : ℕ) : chamberBound H d ≤ chamberBound (H+1) d := by
  cases d with
  | zero => simp [chamber_zero_dimension]
  | succ d => rw [chamber_recurrence]; omega

/-- The binomial bound for actual realized sign chambers in any convex domain.
Neither the geometric insertion inequality nor the dimension reduction is a
hypothesis. Repeated, parallel and zero restricted rows are allowed. -/
theorem arrangement_count_bound (H : ℕ) :
    ∀ (E : Type*) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
      (U : Set E), Convex ℝ U → ∀ (L : Fin H → E →ₗ[ℝ] ℝ) (a : Fin H → ℝ),
      (patterns U (fun i => L i) a).card ≤ chamberBound H (Module.finrank ℝ E) := by
  induction H with
  | zero =>
    intro E _ _ _ U hU L a
    rw [chamber_zero_hyperplanes]
    have h := Finset.card_le_univ (patterns U (fun i => L i) a)
    simpa using h
  | succ H ih =>
    intro E _ _ _ U hU L a
    rw [patterns_succ_card]
    have hold := ih E U hU (fun i => L i.succ) (fun i => a i.succ)
    by_cases hg : L 0=0
    · exact (zero_insertion U (fun i : Fin H => L i.succ) (fun i => a i.succ) (L 0) (a 0) hg).trans
        (hold.trans (bound_mono_hyperplanes H _))
    · have hproper : ∃ v,L 0 v≠0 := by
        by_contra hn
        push_neg at hn
        apply hg
        ext v
        exact hn v
      obtain ⟨v,hv⟩ := hproper
      let p := (a 0/L 0 v) • v
      have hp : L 0 p=a 0 := by simp [p,map_smul,hv]
      have hsection := ih (L 0).ker {v : (L 0).ker | p+(v:E)∈U}
        (section_convex U hU (L 0) p)
        (fun i => L i.succ ∘ₗ (L 0).ker.subtype) (fun i => a i.succ-L i.succ p)
      rw [← section_patterns U (fun i : Fin H => L i.succ) (fun i => a i.succ) (L 0) (a 0) p hp] at hsection
      have hins := insertion_inequality U hU (fun i : Fin H => L i.succ) (fun i => a i.succ) (L 0) (a 0)
      apply hins.trans
      apply (Nat.add_le_add hold hsection).trans
      rw [kernel_dimension (L 0) ⟨v,hv⟩,chamber_recurrence]


theorem patterns_reindex {E ι ν : Type*} [Fintype ι] [Fintype ν]
    (U : Set E) (L : ι → E → ℝ) (a : ι → ℝ) (e : ι ≃ ν) :
    (patterns U (fun j => L (e.symm j)) (fun j => a (e.symm j))).card =
      (patterns U L a).card := by
  classical
  apply Finset.card_bij (fun (s : ν → Bool) _ => fun i => s (e i))
  · intro s hs
    rw [mem_patterns] at hs ⊢
    obtain ⟨x,hx,h⟩ := hs
    exact ⟨x,hx,fun i => by simpa using h (e i)⟩
  · intro s hs t ht he
    ext j
    simpa using congrFun he (e.symm j)
  · intro s hs
    refine ⟨fun j => s (e.symm j),?_,by ext i; simp⟩
    rw [mem_patterns] at hs ⊢
    obtain ⟨x,hx,h⟩ := hs
    exact ⟨x,hx,fun j => h (e.symm j)⟩

theorem finite_arrangement_bound {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι]
    (U : Set E) (hU : Convex ℝ U) (L : ι → E →ₗ[ℝ] ℝ) (a : ι → ℝ) :
    (patterns U (fun i => L i) a).card ≤ chamberBound (Fintype.card ι) (Module.finrank ℝ E) := by
  classical
  let e := Fintype.equivFin ι
  have h := arrangement_count_bound (Fintype.card ι) E U hU
    (fun j => L (e.symm j)) (fun j => a (e.symm j))
  rwa [patterns_reindex U (fun i => L i) a e] at h

noncomputable def closedChambers {σ ι : Type*} [Fintype σ] [Fintype ι]
    (U : Set (σ → ℝ)) (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) : Finset (Set (σ → ℝ)) := by
  classical
  exact (patterns U (fun i => L i) a).image (fun s => closure (CoverAssembly.strictRegion U L a s))

/-- Passing from retained sign regions to their closures cannot increase
the number, even if two descriptions happen to represent the same set. -/
theorem closed_chamber_count {σ ι : Type*} [Fintype σ] [Fintype ι]
    (U : Set (σ → ℝ)) (hU : Convex ℝ U)
    (L : ι → (σ → ℝ) →ₗ[ℝ] ℝ) (a : ι → ℝ) :
    (closedChambers U L a).card ≤ chamberBound (Fintype.card ι) (Fintype.card σ) := by
  classical
  have h := finite_arrangement_bound U hU L a
  have h' := Finset.card_image_le (s:=patterns U (fun i => L i) a)
    (f:=fun s => closure (CoverAssembly.strictRegion U L a s))
  simpa [closedChambers] using h'.trans h

theorem slackInterior_convex {σ κ : Type*} [Fintype σ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi : ℕ) :
    Convex ℝ (CoverAssembly.slackInterior A b Phi) := by
  intro x hx y hy u v hu hv huv i
  have hxlo := (hx i).1
  have hxhi := (hx i).2
  have hylo := (hy i).1
  have hyhi := (hy i).2
  have he : CoverAssembly.slack A b (u • x+v • y) i =
      u*CoverAssembly.slack A b x i+v*CoverAssembly.slack A b y i := by
    unfold CoverAssembly.slack
    simp only [map_add,map_smul,smul_eq_mul]
    have hb := congrArg (fun t : ℝ => t*((b i:ℝ)+1/2)) huv
    nlinarith
  rw [he]
  by_cases hu0 : u=0
  · subst u; simp at huv; subst v; simpa using hy i
  · have hupos := lt_of_le_of_ne hu (Ne.symm hu0)
    have h1 := mul_lt_mul_of_pos_left hxlo hupos
    have h2 := mul_le_mul_of_nonneg_left hylo.le hv
    have h3 := mul_lt_mul_of_pos_left hxhi hupos
    have h4 := mul_le_mul_of_nonneg_left hyhi.le hv
    have h5 := congrArg (fun t : ℝ => t*(2:ℝ)^Phi) huv
    constructor <;> nlinarith

theorem bound_mono (d : ℕ) : Monotone (fun H => chamberBound H d) :=
  monotone_nat_of_le_succ (fun H => bound_mono_hyperplanes H d)

/-- The paper's explicit hyperplane bound now bounds the actual finite family
of retained closed shifted-slack chambers. -/
theorem shifted_chamber_count {σ κ : Type*} [Fintype σ] [Fintype κ]
    (A : κ → σ → ℤ) (b : κ → ℤ) (Phi ell : ℕ) :
    (closedChambers (CoverAssembly.slackInterior A b Phi)
      (fun p : κ × CoverAssembly.Endpoint Phi ell => -LineRestriction.integerRow (A p.1))
      (fun p => p.2.val-(b p.1:ℝ)-1/2)).card ≤
    chamberBound (Fintype.card κ*((Phi+2)*ell+1)) (Fintype.card σ) := by
  have h := closed_chamber_count (CoverAssembly.slackInterior A b Phi) (slackInterior_convex A b Phi)
    (fun p : κ × CoverAssembly.Endpoint Phi ell => -LineRestriction.integerRow (A p.1))
    (fun p => p.2.val-(b p.1:ℝ)-1/2)
  apply h.trans
  apply bound_mono
  simpa [CoverAssembly.Endpoint,Fintype.card_prod] using hyperplane_count (Fintype.card κ) Phi ell

end ChamberInsertion



