/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-!
# Étale sheaves supported in low dimension

Let `B` be a scheme of finite type over a field `K` and `N` a torsion abelian étale sheaf on `B`
whose geometric stalks vanish at every point `y` with `trdeg_K κ(y) > a`. For a closed subset
`Z ⊆ B` with open complement `j_Z : B ∖ Z ⟶ B`, let `N_Z = ker(N ⟶ j_Z* j_Z^* N)` be the
subsheaf of sections supported in `Z`. Then `N` is the filtered union of the `N_Z` over the
closed `Z` of dimension at most `a` (`AlgebraicGeometry.Etale.exists_covering_supportedIn`,
blueprint `lem-sc-support-dimension-union`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-- The ring homomorphism `K ⟶ κ(y)` from the ground field `K` of a `K`-scheme `B` (with
structure morphism `b`) to the residue field at a point `y` of `B`. -/
noncomputable def residueFieldHomOfOver {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : K →+* B.residueField y :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫ B.presheaf.germ ⊤ y trivial ≫
    B.residue y).hom

/-- The transcendence degree `trdeg_K κ(y)` of the residue field at a point `y` of a `K`-scheme
`B` (with structure morphism `b`). -/
noncomputable def residueFieldTrdeg {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : Cardinal.{u} :=
  letI := (residueFieldHomOfOver b y).toAlgebra
  Algebra.trdeg K (B.residueField y)

end Scheme

namespace Etale

variable {B : Scheme.{u}}

/-- The subsheaf `N_Z = ker(N ⟶ j_* j^* N)` of sections of `N` supported in the closed
complement of an open `U` of `B`, where `j : U ⟶ B` is the inclusion. -/
noncomputable def supportedIn (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N)

/-- The inclusion `N_Z ⟶ N` of the sections supported in the complement of `U`. -/
noncomputable def supportedInι (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : supportedIn N U ⟶ N :=
  kernel.ι _

private theorem residueFieldHomOfOver_eq {K : Type u} [Field K]
    (b : B ⟶ Spec (.of K)) (y : B) :
    Scheme.residueFieldHomOfOver b y = b.residueFieldAlgebraMap y := by
  have hm :
      CommRingCat.ofHom (algebraMap (CommRingCat.of K)
        (b y).asIdeal.ResidueField) ≫
          (Scheme.Spec.residueFieldIso (.of K) (b y)).inv ≫ b.residueFieldMap y =
        (Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫
          B.presheaf.germ ⊤ y trivial ≫ B.residue y := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv_assoc,
      Scheme.residue_residueFieldMap]
    rw [Scheme.Hom.germ_stalkMap_assoc]
    rfl
  exact congrArg CommRingCat.Hom.hom hm.symm

private theorem dim_finite_union_le {X : Type u} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {ι : Type*} (I : Finset ι) (C : ι → Set X)
    (hC : ∀ i ∈ I, IsClosed (C i)) (a : WithBot ℕ∞)
    (hCa : ∀ i ∈ I, topologicalKrullDim (C i) ≤ a) :
    topologicalKrullDim (⋃ i ∈ I, C i) ≤ a := by
  have : QuasiSober (⋃ i ∈ I, C i) :=
    (isClosed_biUnion_finset hC).isClosedEmbedding_subtypeVal.quasiSober
  let := specializationOrder (⋃ i ∈ I, C i)
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDim_closure_singleton]
  obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp z.property
  have hc : closure ({z} : Set (⋃ i ∈ I, C i)) ⊆ Subtype.val ⁻¹' C i :=
    closure_minimal (Set.singleton_subset_iff.mpr hz)
      ((hC i hi).preimage continuous_subtype_val)
  let f : closure ({z} : Set (⋃ i ∈ I, C i)) → C i :=
    fun x ↦ ⟨x.val.val, hc x.property⟩
  have hf : Topology.IsInducing f := by
    apply (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : C i → X)).of_comp_iff.mp
    change Topology.IsInducing (fun x : closure ({z} : Set (⋃ i ∈ I, C i)) ↦ x.val.val)
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  exact hf.topologicalKrullDim_le.trans (hCa i hi)

private theorem exists_closed_image_bound {K : Type u} [Field K]
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [QuasiCompact b]
    (a : ℕ) {Y : Scheme.{u}} [TopologicalSpace.NoetherianSpace Y] (f : Y ⟶ B)
    (S : Set Y) (hS : IsClosed S)
    (hbound : ∀ y ∈ S, Scheme.residueFieldTrdeg b (f y) ≤ (a : Cardinal.{u})) :
    ∃ Z : Set B, IsClosed Z ∧ topologicalKrullDim Z ≤ a ∧ f '' S ⊆ Z := by
  classical
  let overB : B.Over (Spec (.of K)) := ⟨b⟩
  have : LocallyOfFiniteType (B ↘ Spec (.of K)) := ‹LocallyOfFiniteType b›
  have : QuasiCompact (B ↘ Spec (.of K)) := ‹QuasiCompact b›
  obtain ⟨C, hCf, hCc, hCi, hCS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  choose η hη using fun c : C ↦ QuasiSober.sober (hCi c c.property) (hCc c c.property)
  let : Fintype C := hCf.fintype
  let I : Finset B := Finset.univ.image fun c : C ↦ f (η c)
  refine ⟨⋃ y ∈ I, closure ({y} : Set B),
    isClosed_biUnion_finset fun _ _ ↦ isClosed_closure, ?_, ?_⟩
  · apply dim_finite_union_le I (fun y ↦ closure ({y} : Set B))
      (fun _ _ ↦ isClosed_closure)
    intro y hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hd, htr⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg (K := K)
      (closure ({f (η c)} : Set B)) isClosed_closure
      isIrreducible_singleton.closure (f (η c)) (subset_closure (by simp)) rfl
    rw [hd]
    have ht := hbound (η c) (hCS ▸ Set.mem_sUnion_of_mem (hη c).mem c.property)
    unfold Scheme.residueFieldTrdeg at ht
    rw [residueFieldHomOfOver_eq] at ht
    rw [htr] at ht
    exact_mod_cast ht
  · rintro _ ⟨y, hy, rfl⟩
    rw [hCS] at hy
    obtain ⟨c, hc, hyc⟩ := Set.mem_sUnion.mp hy
    refine Set.mem_iUnion₂.mpr ⟨f (η ⟨c, hc⟩), Finset.mem_image.mpr
      ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    exact specializes_iff_mem_closure.mp (((hη ⟨c, hc⟩).specializes hyc).map f.continuous)

set_option backward.isDefEq.respectTransparency false in
private theorem trdeg_le_of_not_vanishing {K : Type u} [Field K]
    (b : B ⟶ Spec (.of K)) (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N))
    (V : B.Etale) (s : N.obj.obj (Opposite.op V)) (y : V.left)
    (hy : y ∉ vanishingLocus N s) :
    Scheme.residueFieldTrdeg b (V.hom y) ≤ (a : Cardinal.{u}) := by
  by_contra! h
  let Ω := AlgebraicClosure (V.left.residueField y)
  let v := V.left.algClosurePoint y
  let t := v ≫ V.hom
  have hz : IsZero ((t)^*[AddCommGrpCat.{u + 1}].obj N) :=
    hstalk Ω t (by
      change (a : Cardinal) < Scheme.residueFieldTrdeg b (V.hom (v _))
      rw [show v (IsLocalRing.closedPoint Ω) = y from Scheme.algClosurePoint_base _ _ _]
      exact h)
  let E : (Spec (.of Ω)).Etale := Scheme.Etale.mk (𝟙 _)
  have hobj : IsZero (((t)^*[AddCommGrpCat.{u + 1}].obj N).obj.obj (Opposite.op E)) :=
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (Opposite.op E)).map_isZero hz
  let := AddCommGrpCat.subsingleton_of_isZero hobj
  have hzero : pullSection t N (V := E) v
      (by change v ≫ V.hom = (𝟙 _) ≫ t; exact (Category.id_comp t).symm) s = 0 :=
    Subsingleton.elim _ _
  have hv := range_subset_vanishingLocus_of_pullSection_eq_zero t N (V := E) v
    (by change v ≫ V.hom = (𝟙 _) ≫ t; exact (Category.id_comp t).symm) s
    hzero ⟨IsLocalRing.closedPoint Ω, rfl⟩
  apply hy
  change v (IsLocalRing.closedPoint Ω) ∈ vanishingLocus N s at hv
  rwa [show v (IsLocalRing.closedPoint Ω) = y from Scheme.algClosurePoint_base _ _ _] at hv

set_option backward.isDefEq.respectTransparency false in
private theorem unit_section_eq_zero_of_range {N :
    Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {V : B.Etale} (s : N.obj.obj (Opposite.op V)) (U : B.Opens)
    (h : ∀ y : V.left, V.hom y ∈ U → y ∈ vanishingLocus N s) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app _ s = 0 := by
  let P : (U : Scheme).Etale := (MorphismProperty.Over.pullback @Etale ⊤ U.ι).obj V
  let E : B.Etale := Scheme.Etale.mk (pullback.fst V.hom U.ι ≫ V.hom)
  let g : E ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom U.ι) rfl
  have hzero : N.obj.map g.op s = 0 := by
    apply eq_zero_of_forall_mem_vanishingLocus
    intro y
    rw [vanishingLocus_map]
    apply h
    have he := congrArg (fun f : E.left ⟶ B ↦ f y) (pullback.condition (f := V.hom) (g := U.ι))
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
    change V.hom ((pullback.fst V.hom U.ι) y) ∈ U
    exact he.symm ▸ (pullback.snd V.hom U.ι y).property
  let F := ((U.ι)^*[AddCommGrpCat.{u + 1}].obj N)
  let z : F.obj.obj (Opposite.op P) :=
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app _ s
  have h₁ : F.obj.map (𝟙 (Opposite.op P)) z =
      pullSection U.ι N (V := P) (pullback.fst V.hom U.ι) (pullback.condition) s :=
    map_unit_app_eq_pullSection U.ι N (𝟙 P) s
  have hid : F.obj.map (𝟙 (Opposite.op P)) = 𝟙 _ := F.obj.map_id _
  have hE : (𝟙 E.left) ≫ E.hom = P.hom ≫ U.ι := by
    change (𝟙 _) ≫ (pullback.fst V.hom U.ι ≫ V.hom) = pullback.snd V.hom U.ι ≫ U.ι
    exact (Category.id_comp _).trans pullback.condition
  have h₂ := pullSection_comp U.ι N g (V := P) (𝟙 E.left) hE s
  have hi : (𝟙 E.left) ≫ g.left = pullback.fst V.hom U.ι := Category.id_comp _
  have hcomp : (𝟙 E.left ≫ g.left) ≫ V.hom = P.hom ≫ U.ι :=
    (Category.assoc _ _ _).trans hE
  have hleft := pullSection_congr U.ι N (V := P) (U := V)
    (φ := 𝟙 E.left ≫ g.left) (φ' := pullback.fst V.hom U.ι) hcomp hi s
  have h₂' := hleft.symm.trans h₂
  change z = 0
  calc
    z = F.obj.map (𝟙 (Opposite.op P)) z :=
      congrArg (fun k : F.obj.obj (Opposite.op P) ⟶ F.obj.obj (Opposite.op P) ↦ k z) hid.symm
    _ = _ := h₁
    _ = _ := h₂'
    _ = 0 := by rw [hzero]; exact pullSection_zero _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The geometric support argument before taking the kernel lift.

Source: Stacks Project, Étale Cohomology, Tag 04FR, together with the finite-type
dimension argument in Tag 0B1C.  It says that, after an étale refinement, the
restriction of a section to the complement of a closed set of bounded dimension
vanishes.  The final lift through `supportedIn` is a separate formal kernel
construction in `exists_covering_supportedIn`.
-/
private theorem exists_covering_section_zero_off_closed {K : Type u} [Field K]
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] [QuasiCompact b] (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (_hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N)) :
    ∀ (V : B.Etale) (s : N.obj.obj (Opposite.op V)), ∃ R ∈ B.smallEtaleTopology V,
      ∀ ⦃W : B.Etale⦄ (g : W ⟶ V), R g → ∃ (U : B.Opens)
        (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a),
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app _
          (N.obj.map g.op s) = 0 := by
  classical
  intro V s
  let R : Sieve V :=
    { arrows := fun W g ↦ ∃ U : B.Opens,
        topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a ∧
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app _
            (N.obj.map g.op s) = 0
      downward_closed := by
        intro W W' g hg f
        obtain ⟨U, hU, hz⟩ := hg
        refine ⟨U, hU, ?_⟩
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        exact (NatTrans.naturality_apply
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom
          f.op _).trans (by rw [hz, map_zero]) }
  refine ⟨R, (Scheme.mem_smallEtaleTopology_iff R).mpr ?_, ?_⟩
  · intro x
    obtain ⟨i, y, hy⟩ := V.left.affineCover.exists_eq x
    let W : B.Etale := Scheme.Etale.mk (V.left.affineCover.f i ≫ V.hom)
    let g : W ⟶ V := MorphismProperty.Over.homMk (V.left.affineCover.f i) rfl
    have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian b
    have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian (Y := B) W.hom
    have : IsAffine W.left := inferInstanceAs (IsAffine (V.left.affineCover.X i))
    have : IsNoetherian W.left := ⟨⟩
    have : TopologicalSpace.NoetherianSpace W.left := inferInstance
    obtain ⟨Z, hZ, hZa, hSZ⟩ := exists_closed_image_bound b a (Y := W.left) W.hom
      (vanishingLocus N (N.obj.map g.op s))ᶜ
      (isOpen_vanishingLocus _).isClosed_compl
      (fun z hz ↦ trdeg_le_of_not_vanishing b a N hstalk W _ z hz)
    let U : B.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
    refine ⟨W, g, ⟨U, ?_, ?_⟩, ⟨y, hy⟩⟩
    · change topologicalKrullDim (Zᶜᶜ : Set B) ≤ a
      rwa [compl_compl]
    · apply unit_section_eq_zero_of_range
      intro z hz
      by_contra hnonzero
      exact hz (hSZ ⟨z, hnonzero, rfl⟩)
  · intro W g hg
    obtain ⟨U, hU, hz⟩ := hg
    exact ⟨U, hU, hz⟩

/-- Blueprint `lem-sc-support-dimension-union`: A sheaf supported in low dimension is a filtered
union.

Let `B` be a scheme of finite type over a field `K` (structure morphism `b`), `a ≥ 0`, and `N` a
torsion abelian étale sheaf on `B` with zero geometric stalk at every point `y` with
`trdeg_K κ(y) > a`: for every separably closed field `Ω` and every geometric point
`s : Spec Ω ⟶ B` lying over such a `y`, `s^* N = 0`. For a closed `Z ⊆ B` with complement
`j_Z : B ∖ Z ⟶ B` let `N_Z = ker(N ⟶ j_Z* j_Z^* N)`. Then `N` is the union of the subsheaves
`N_Z` over the closed `Z` of dimension at most `a`: every section of `N` lies, locally on an
étale covering, in some `N_Z`. Since the `N_Z ⟶ N` are monomorphisms and the closed sets of
dimension at most `a` form a directed system under finite unions, this says that the canonical
map `colim_Z N_Z ⟶ N` is an isomorphism, which is the blueprint's formulation. -/
theorem exists_covering_supportedIn {K : Type u} [Field K] (b : B ⟶ Spec (.of K))
    [LocallyOfFiniteType b] [QuasiCompact b] (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N)) :
    ∀ (V : B.Etale) (s : N.obj.obj (Opposite.op V)), ∃ R ∈ B.smallEtaleTopology V,
      ∀ ⦃W : B.Etale⦄ (g : W ⟶ V), R g → ∃ (U : B.Opens)
        (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
        (t : (supportedIn N U).obj.obj (Opposite.op W)),
          (supportedInι N U).hom.app _ t = N.obj.map g.op s := by
  intro V s
  obtain ⟨R, hR, hRs⟩ := exists_covering_section_zero_off_closed b a N hN hstalk V s
  refine ⟨R, hR, fun W g hg ↦ ?_⟩
  obtain ⟨U, hU, hz⟩ := hRs g hg
  obtain ⟨t, ht⟩ := exists_kernel_ι_app_eq
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N)
    (N.obj.map g.op s) hz
  exact ⟨U, hU, t, ht⟩

end Etale

end AlgebraicGeometry
