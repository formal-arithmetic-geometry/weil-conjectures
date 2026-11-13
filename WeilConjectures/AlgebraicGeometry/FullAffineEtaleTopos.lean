/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Affine étale restriction and cohomology

## References

* Stacks Project, Topologies 04HR, Definitions 0219 and 021B(4), and
  Cohomology on Sites 03YU.
-/

@[expose] public section


universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace AlgebraicGeometry.Scheme

private theorem fullAffineEtale_preservesPullbacks (S : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (fullAffineEtaleInclusion S) := by
  let P : ObjectProperty S.Etale := fun U => IsAffine U.left
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := ⟨by
    rintro X ⟨h⟩
    let F := Etale.forget S ⋙ Over.forget S
    have (j : WalkingCospan) : IsAffine ((h.diag ⋙ F).obj j) := h.prop_diag_obj j
    exact Scheme.isAffine_of_isLimit (F.mapCone h.toLimitPresentation.cone)
      (isLimitOfPreserves F h.isLimit)⟩
  exact
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan P.ι)

/-- A sheaf on the small étale site restricts to a sheaf for the full affine étale topology.
(Stacks, Tags 04HR, 021E) -/
theorem fullAffineEtaleInclusion_continuity_sheaf_condition (S : Scheme.{u}) :
    ∀ G : Sheaf S.smallEtaleTopology (Type (u + 1)),
      Presieve.IsSheaf
        (fullAffineEtaleTopology S)
        ((fullAffineEtaleInclusion S).op ⋙ G.obj) := by
  obtain ⟨J, hJ⟩ := fullAffineEtalePrecoverage_isPretopology S
  have := fullAffineEtale_preservesPullbacks S
  intro G
  change Presieve.IsSheaf (fullAffineEtalePrecoverage S).toGrothendieck _
  rw [← hJ]
  change Presieve.IsSheaf J.toCoverage.toPrecoverage.toGrothendieck
    ((fullAffineEtaleInclusion S).op ⋙ G.obj)
  rw [Coverage.toGrothendieck_toPrecoverage, J.toGrothendieck_toCoverage,
    Presieve.isSheaf_pretopology]
  intro U R hR
  have hR' : R ∈ fullAffineEtalePrecoverage S U := by simpa [hJ] using hR
  obtain ⟨n, V, f, rfl, hf, hsurj⟩ := hR'
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  apply ((isSheaf_iff_isSheaf_of_type _ _).mp G.property).isSheafFor
  rw [Presieve.map_ofArrows]
  apply (Scheme.ofArrows_mem_smallEtaleTopology_iff _).mpr
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact hsurj x

/-- The inclusion of the full affine étale site into the small étale site is continuous.
(Stacks, Tag 04HR) -/
theorem fullAffineEtaleInclusion_isContinuous (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsContinuous
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  exact { op_comp_isSheaf_of_types := fullAffineEtaleInclusion_continuity_sheaf_condition S }

attribute [instance] fullAffineEtaleInclusion_isContinuous

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem fullAffineEtale_cover_refinement (S : Scheme.{u})
    (U : S.FullAffineEtale) (R : Sieve U.obj) (hR : R ∈ S.smallEtaleTopology U.obj) :
    ∃ (T : Presieve U), T ∈ fullAffineEtalePrecoverage S U ∧
      T.map (fullAffineEtaleInclusion S) ≤ R.arrows := by
  classical
  have : IsAffine U.obj.left := U.property
  obtain ⟨𝒰, hOver, hp, hle⟩ := (S.mem_smallGrothendieckTopology U.obj R).mp hR
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i => (𝒰.f i).isOpenMap)
  obtain ⟨𝒱, a, hfin, hopen⟩ := QuasiCompactCover.exists_hom 𝒰
  let := Fintype.ofFinite 𝒱.I₀
  have (j : 𝒱.I₀) : AlgebraicGeometry.Etale (𝒱.f j) := 𝒱.cover.map_prop j
  have : AlgebraicGeometry.Etale U.obj.hom := U.obj.prop
  let e := Fintype.equivFin 𝒱.I₀
  let V : Fin (Fintype.card 𝒱.I₀) → S.FullAffineEtale := fun i =>
    ⟨Scheme.Etale.mk (𝒱.f (e.symm i) ≫ U.obj.hom), by
      change IsAffine (Spec _)
      infer_instance⟩
  let f : ∀ i, V i ⟶ U := fun i =>
    ObjectProperty.homMk (MorphismProperty.Over.homMk (𝒱.f (e.symm i)))
  refine ⟨Presieve.ofArrows V f, ⟨_, V, f, rfl, ?_, ?_⟩, ?_⟩
  · intro i
    exact 𝒱.cover.map_prop (e.symm i)
  · intro x
    obtain ⟨j, y, hy⟩ := 𝒱.cover.exists_eq x
    refine ⟨e j, ?_⟩
    change ∃ y : Spec (𝒱.X (e.symm (e j))), (𝒱.f (e.symm (e j))) y = x
    rw [e.symm_apply_apply]
    exact ⟨y, hy⟩
  · rw [Presieve.map_ofArrows]
    rintro Y g ⟨i⟩
    let j := e.symm i
    let b : (fullAffineEtaleInclusion S).obj (V i) ⟶
        (𝒰.X (a.s₀ j)).asOverProp S (hp (a.s₀ j)) :=
      MorphismProperty.Over.homMk (a.h₀ j) (by
        change a.h₀ j ≫ (𝒰.X (a.s₀ j) ↘ S) = 𝒱.f j ≫ U.obj.hom
        calc
          _ = a.h₀ j ≫ 𝒰.f (a.s₀ j) ≫ U.obj.hom := by
            congr 1
            exact (CategoryTheory.comp_over (𝒰.f (a.s₀ j)) S).symm
          _ = _ := by rw [← Category.assoc]; exact congrArg (· ≫ U.obj.hom) (a.w₀ j))
    have hb : b ≫ (𝒰.f (a.s₀ j)).asOverProp S =
        (fullAffineEtaleInclusion S).map (f i) := by
      apply MorphismProperty.Over.Hom.ext
      exact a.w₀ j
    rw [← hb]
    exact R.downward_closed (hle _ _ ⟨a.s₀ j⟩) b

private theorem fullAffineEtale_image_cover (S : Scheme.{u}) (V : S.Etale) :
    ∃ (I : Type u) (U : I → S.FullAffineEtale)
      (f : ∀ i, (fullAffineEtaleInclusion S).obj (U i) ⟶ V),
      Sieve.ofArrows _ f ∈ S.smallEtaleTopology V := by
  let E := (AffineEtale.Spec S).oneHypercoverDenseData.{u}
    (AffineEtale.topology S) S.smallEtaleTopology V
  let U : E.I₀ → S.FullAffineEtale := fun i =>
    ⟨(AffineEtale.Spec S).obj (E.X i), by change IsAffine (Spec _); infer_instance⟩
  exact ⟨E.I₀, U, E.f, E.mem₀⟩

private theorem fullAffineEtale_cover_dense (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsCoverDense S.smallEtaleTopology := by
  constructor
  intro V
  obtain ⟨I, U, f, hf⟩ := fullAffineEtale_image_cover S V
  apply S.smallEtaleTopology.superset_covering _ hf
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro W g ⟨i⟩
  exact Presieve.in_coverByImage _ (f i)

set_option backward.isDefEq.respectTransparency false in
private theorem fullAffineEtale_topology_eq_induced (S : Scheme.{u}) :
    fullAffineEtaleTopology S =
      (fullAffineEtaleInclusion S).inducedTopology S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  apply le_antisymm
  · rw [Functor.le_inducedTopology_iff]
    infer_instance
  · intro U R hR
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense] at hR
    obtain ⟨T, hT, hle⟩ := fullAffineEtale_cover_refinement S U _ hR
    have hTR : T ≤ R.arrows := by
      intro V f hf
      have h := hle _ _ (Presieve.map.of hf)
      obtain ⟨W, g, i, hg, hi⟩ := h
      have hfac : (fullAffineEtaleInclusion S).preimage i ≫ g = f := by
        apply (fullAffineEtaleInclusion S).map_injective
        simpa using hi.symm
      rw [← hfac]
      exact R.downward_closed hg _
    exact (fullAffineEtaleTopology S).superset_covering
      ((Sieve.generate_le_iff _ _).mpr hTR) (Precoverage.generate_mem_toGrothendieck hT)

private theorem fullAffineEtale_dense_subsite (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsDenseSubsite
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  rw [fullAffineEtale_topology_eq_induced]
  infer_instance

private theorem fullAffineEtale_oneHypercover_dense (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsOneHypercoverDense.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
  have := fullAffineEtale_cover_dense S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  have hd : (fullAffineEtaleInclusion S).IsDenseSubsite
      (fullAffineEtaleTopology S) S.smallEtaleTopology := by
    rw [fullAffineEtale_topology_eq_induced]
    infer_instance
  exact Functor.IsOneHypercoverDense.of_hasPullbacks (fullAffineEtale_image_cover S)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem smallEtale_cover_of_surjective (S : Scheme.{u})
    {I : Type u} (V : I → S.Etale) (U : S.Etale) (f : ∀ i, V i ⟶ U)
    (h : ∀ x : U.left, ∃ i y, (f i).left y = x) :
    Presieve.ofArrows V f ∈ S.smallEtalePretopology U := by
  change ((Presieve.ofArrows V f).map (MorphismProperty.Over.forget
    (@AlgebraicGeometry.Etale) ⊤ S)).map (Over.forget S) ∈
      Scheme.precoverage (@AlgebraicGeometry.Etale) U.left
  rw [Presieve.map_ofArrows, Presieve.map_ofArrows, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨h, fun i ↦ ?_⟩
  change AlgebraicGeometry.Etale (f i).left
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion of the full affine étale site is special cocontinuous for the affine étale
coverings and the small étale pretopology. (Stacks, Tags 04HR, 021E; Sites, Tag 03A0) -/
theorem fullAffineEtale_special_cocontinuity (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsSpecialCocontinuousForCoverings
      (fullAffineEtalePrecoverage S) S.smallEtalePretopology.toPrecoverage := by
  have hd := fullAffineEtale_dense_subsite S
  have := fullAffineEtale_preservesPullbacks S
  have : (fullAffineEtaleInclusion S).Full :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Full
  have : (fullAffineEtaleInclusion S).Faithful :=
    inferInstanceAs (ObjectProperty.ι (fun U : S.Etale => IsAffine U.left)).Faithful
  have htop : S.smallEtalePretopology.toPrecoverage.toGrothendieck =
      S.smallEtaleTopology := by
    change S.smallEtalePretopology.toCoverage.toPrecoverage.toGrothendieck = _
    rw [Coverage.toGrothendieck_toPrecoverage, Pretopology.toGrothendieck_toCoverage]
    exact (S.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology
      (P := @AlgebraicGeometry.Etale) le_rfl).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (fullAffineEtaleInclusion S).IsCocontinuous
      (fullAffineEtaleTopology S) S.smallEtalePretopology.toPrecoverage.toGrothendieck
    rw [htop]
    infer_instance
  · intro U R hR
    obtain ⟨n, V, f, rfl, hf, hsurj⟩ := hR
    rw [Presieve.map_ofArrows]
    have hh := smallEtale_cover_of_surjective S
      (fun i : ULift.{u} (Fin n) => (V i.down).obj) U.obj
      (fun i => (f i.down).hom) (by
        intro x
        obtain ⟨i, y, hy⟩ := hsurj x
        exact ⟨⟨i⟩, y, hy⟩)
    have heq : Presieve.ofArrows (fun i : ULift.{u} (Fin n) => (V i.down).obj)
        (fun i => (f i.down).hom) = Presieve.ofArrows (fun i => (V i).obj)
        (fun i => (f i).hom) :=
      Presieve.ofArrows_comp_eq_of_surjective (fun i => (f i).hom)
        (a := ULift.down) (fun i => ⟨⟨i⟩, rfl⟩)
    exact (congrArg (· ∈ S.smallEtalePretopology U.obj) heq).mp hh
  · intro X Y Z R hR f g hf
    infer_instance
  · intro X Y a b hab
    have heq : a = b := (fullAffineEtaleInclusion S).map_injective hab
    obtain ⟨J, hJ⟩ := fullAffineEtalePrecoverage_isPretopology S
    refine ⟨Presieve.singleton (𝟙 X), ?_, ?_⟩
    · rw [← hJ]
      exact J.has_isos _
    · intro Z f hf
      rw [heq]
  · intro X Y c
    obtain ⟨J, hJ⟩ := fullAffineEtalePrecoverage_isPretopology S
    refine ⟨Presieve.singleton (𝟙 X), ?_, ?_⟩
    · rw [← hJ]
      exact J.has_isos _
    · intro Z f hf
      exact ⟨f ≫ (fullAffineEtaleInclusion S).preimage c, by simp⟩
  · intro V
    obtain ⟨I, U, f, hf⟩ := fullAffineEtale_image_cover S V
    have hsurj : ∀ x : V.left, ∃ i y, (f i).left y = x := by
      have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mp hf
      intro x
      have hx : x ∈ ⋃ i, Set.range (f i).left := by rw [h]; trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hx
    refine ⟨ULift.{u + 1} I, (fun i => U i.down), (fun i => f i.down), ?_⟩
    have heq : Presieve.ofArrows
        (fun i : ULift.{u + 1} I => (fullAffineEtaleInclusion S).obj (U i.down))
        (fun i => f i.down) = Presieve.ofArrows _ f :=
      Presieve.ofArrows_comp_eq_of_surjective f (a := ULift.down)
        (fun i => ⟨⟨i⟩, rfl⟩)
    exact (congrArg (· ∈ S.smallEtalePretopology V) heq).mpr
      (smallEtale_cover_of_surjective S _ _ _ hsurj)

/-- Restriction along the full affine inclusion is an equivalence on sheaves of sets.
(Stacks, Tag 04HR) -/
theorem fullAffineEtale_sets_equivalence (S : Scheme.{u}) :
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type u)
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by
  have := fullAffineEtale_oneHypercover_dense S
  have := fullAffineEtale_dense_subsite S
  exact Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/-- Restriction along the full affine inclusion is an equivalence on sheaves of abelian groups.
(Stacks, Tag 04HR) -/
theorem fullAffineEtale_ab_equivalence (S : Scheme.{u}) :
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by
  have := fullAffineEtale_oneHypercover_dense S
  have := fullAffineEtale_dense_subsite S
  exact Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/-- The full affine inclusion is special cocontinuous, and restriction is an equivalence on
sheaves of sets and of abelian groups. (Stacks, Tag 04HR) -/
theorem fullAffineEtaleInclusion_special_equivalences (S : Scheme.{u}) :
    (fullAffineEtaleInclusion S).IsSpecialCocontinuousForCoverings
      (fullAffineEtalePrecoverage S) S.smallEtalePretopology.toPrecoverage ∧
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous (Type u)
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence ∧
    ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology).IsEquivalence := by
  exact ⟨fullAffineEtale_special_cocontinuity S,
    fullAffineEtale_sets_equivalence S, fullAffineEtale_ab_equivalence S⟩


private noncomputable def affineEtaleFreeSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (op U) (𝟙 U) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

private noncomputable def affineEtaleSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ F).trans
    (affineEtaleFreeSectionsEquiv U F.obj)

private lemma affineEtaleSectionsEquiv_naturality
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C)
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (a : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    affineEtaleSectionsEquiv J U G (a ≫ f) =
      f.hom.app (op U) (affineEtaleSectionsEquiv J U F a) := by
  dsimp only [affineEtaleSectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [affineEtaleFreeSectionsEquiv]
  rfl

private lemma extZero_postcomp {C : Type*} [Category C] [Abelian C]
    [HasExt.{w} C] {X F G : C} (f : F ⟶ G) (x : Ext.{w} X F 0) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0)) = Ext.addEquiv₀ x ≫ f := by
  apply (Ext.mk₀_bijective X G).injective
  simp only [Ext.mk₀_addEquiv₀_apply, ← Ext.mk₀_comp_mk₀]


private noncomputable def affineEtaleHZeroSectionsEquiv
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    Sheaf.H'.{w} F 0 U ≃+ F.obj.obj (op U) :=
  Ext.addEquiv₀.trans (affineEtaleSectionsEquiv J U F)

private lemma affineEtaleHZeroSectionsEquiv_naturality
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]
    (U : C) {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (x : Sheaf.H'.{w} F 0 U) :
    affineEtaleHZeroSectionsEquiv J U G
        (((Sheaf.cohomologyPresheafFunctor J 0).map f).app (op U) x) =
      f.hom.app (op U) (affineEtaleHZeroSectionsEquiv J U F x) := by
  change affineEtaleSectionsEquiv J U G
    (Ext.addEquiv₀ (x.comp (Ext.mk₀ f) (add_zero 0))) = _
  rw [extZero_postcomp, affineEtaleSectionsEquiv_naturality]
  rfl

private theorem affineEtale_free_restriction (S : Scheme.{u}) (U : S.FullAffineEtale) :
    Nonempty ((presheafToSheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
        (fullAffineEtaleTopology S) S.smallEtaleTopology).obj
        ((presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
          (yoneda.obj U.obj ⋙ AddCommGrpCat.free))) := by
  let R := (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
    (fullAffineEtaleTopology S) S.smallEtaleTopology
  have : R.IsEquivalence := fullAffineEtale_ab_equivalence S
  let E := R.asEquivalence
  let X := (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
    (yoneda.obj U.obj ⋙ AddCommGrpCat.free)
  let Y := (presheafToSheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  let a := E.symm.toAdjunction
  let e : coyoneda.obj (op (E.inverse.obj Y)) ≅ coyoneda.obj (op X) :=
    NatIso.ofComponents (fun G =>
      (((a.homEquiv Y G).trans
        (affineEtaleSectionsEquiv (fullAffineEtaleTopology S) U (R.obj G)).toEquiv).trans
        (affineEtaleSectionsEquiv S.smallEtaleTopology U.obj G).toEquiv.symm).toIso) (by
      intro G H f
      ext x
      change (affineEtaleSectionsEquiv S.smallEtaleTopology U.obj H).symm
        (affineEtaleSectionsEquiv (fullAffineEtaleTopology S) U (R.obj H)
          (a.homEquiv Y H (x ≫ f))) =
        (affineEtaleSectionsEquiv S.smallEtaleTopology U.obj G).symm
          (affineEtaleSectionsEquiv (fullAffineEtaleTopology S) U (R.obj G)
            (a.homEquiv Y G x)) ≫ f
      apply (affineEtaleSectionsEquiv S.smallEtaleTopology U.obj H).injective
      rw [AddEquiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
        affineEtaleSectionsEquiv_naturality, affineEtaleSectionsEquiv_naturality,
        AddEquiv.apply_symm_apply]
      rfl)
  let i : E.inverse.obj Y ≅ X := (coyoneda.preimageIso e).unop.symm
  exact ⟨(E.counitIso.app Y).symm ≪≫ R.mapIso i⟩

set_option linter.unusedVariables false in
/-- Cohomology comparison for the restriction equivalence between the small étale site and the
full affine étale site (Stacks, Cohomology on Sites, Tag 03YU, and Topologies, Tag 04HR). -/
theorem fullAffineEtale_cohomology_comparison_data (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) :
    ∃ e : ∀ p : ℕ,
      ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj)), True := by
  classical
  let R := (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
    (fullAffineEtaleTopology S) S.smallEtaleTopology
  have : R.IsEquivalence := fullAffineEtale_ab_equivalence S
  have : R.Additive := ⟨by intros; rfl⟩
  have : EnoughInjectives (Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) := inferInstance
  obtain ⟨i⟩ := affineEtale_free_restriction S U
  let X := (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
    (yoneda.obj U.obj ⋙ AddCommGrpCat.free)
  let m (p : ℕ) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    (Ext.precompAddEquiv i (R.obj G) p).toAddMonoidHom.comp (R.mapExtAddHom X G p)
  have hm (p : ℕ) (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
      Function.Bijective (m p G) :=
    (Ext.precompAddEquiv i (R.obj G) p).bijective.comp
      (R.mapExt_bijective_of_preservesInjectiveObjects X G p)
  let e (p : ℕ) :
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
          (CategoryTheory.evaluation _ _).obj (op U.obj) ≅
      R ⋙ Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) :=
    NatIso.ofComponents (fun G => (AddEquiv.ofBijective (m p G) (hm p G)).toAddCommGrpIso)
      (by
        intro G H f
        ext x
        change (Ext.mk₀ i.hom).comp
          ((x.comp (Ext.mk₀ f) (add_zero p)).mapExactFunctor R) (zero_add p) =
          ((Ext.mk₀ i.hom).comp (x.mapExactFunctor R) (zero_add p)).comp
            (Ext.mk₀ (R.map f)) (add_zero p)
        rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
        exact (Ext.comp_assoc _ _ _ (zero_add p) (add_zero p) (by omega)).symm)
  exact ⟨fun p => (e p).symm, trivial⟩

/-- The cohomology comparison at a point has a normalized degree-zero component.
(Stacks, Tag 03YU) -/
theorem fullAffineEtale_cohomology_comparison_point (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) :
    ∃ e :
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) 0 ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology 0 ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj),
    ∀ (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (x : Sheaf.H'.{w}
        (((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology).obj G) 0 U),
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ _
        (Ext.homEquiv₀ ((e.app G).hom x))).app (op U.obj))
          (FreeAbelianGroup.of (𝟙 U.obj)) =
      (((sheafificationAdjunction (fullAffineEtaleTopology S) AddCommGrpCat.{u}).homEquiv
        _ _ (Ext.homEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U))  := by
  let R := (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
    (fullAffineEtaleTopology S) S.smallEtaleTopology
  let a (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    affineEtaleHZeroSectionsEquiv (fullAffineEtaleTopology S) U (R.obj G)
  let b (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :=
    affineEtaleHZeroSectionsEquiv S.smallEtaleTopology U.obj G
  let e : R ⋙ Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) 0 ⋙
      (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology 0 ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj) :=
    NatIso.ofComponents (fun G => ((a G).trans (b G).symm).toAddCommGrpIso) (by
    intro G H f
    ext x
    change (b H).symm (a H
      (((Sheaf.cohomologyPresheafFunctor (fullAffineEtaleTopology S) 0).map
        (R.map f)).app (op U) x)) =
      ((Sheaf.cohomologyPresheafFunctor S.smallEtaleTopology 0).map f).app (op U.obj)
        ((b G).symm (a G x))
    apply (b H).injective
    rw [AddEquiv.apply_symm_apply]
    change affineEtaleHZeroSectionsEquiv (fullAffineEtaleTopology S) U (R.obj H) _ =
      affineEtaleHZeroSectionsEquiv S.smallEtaleTopology U.obj H _
    rw [affineEtaleHZeroSectionsEquiv_naturality,
      affineEtaleHZeroSectionsEquiv_naturality]
    change f.hom.app (op U.obj) (a G x) =
      f.hom.app (op U.obj) (b G ((b G).symm (a G x)))
    rw [AddEquiv.apply_symm_apply])
  refine ⟨e, ?_⟩
  intro G x
  change b G ((b G).symm (a G x)) = a G x
  exact AddEquiv.apply_symm_apply _ _

/-- Objectwise cohomology comparison between the full affine étale site and the small étale
site, with a normalized degree-zero component. (Stacks, Tags 03YU, 04HR) -/
theorem fullAffineEtale_cohomology_comparison (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) :
    ∃ e : ∀ p : ℕ,
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj),
    ∀ (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (x : Sheaf.H'.{w}
        (((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology).obj G) 0 U),
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ _
        (Ext.homEquiv₀ (((e 0).app G).hom x))).app (op U.obj))
          (FreeAbelianGroup.of (𝟙 U.obj)) =
      (((sheafificationAdjunction (fullAffineEtaleTopology S) AddCommGrpCat.{u}).homEquiv
        _ _ (Ext.homEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U)) := by
  classical
  obtain ⟨d, _⟩ := fullAffineEtale_cohomology_comparison_data S U
  obtain ⟨e₀, h₀⟩ := fullAffineEtale_cohomology_comparison_point S U
  let e : ∀ p : ℕ,
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
        Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
          (CategoryTheory.evaluation _ _).obj (op U.obj) := fun p =>
    match p with
    | 0 => e₀
    | n + 1 => d (n + 1)
  exact ⟨e, h₀⟩

/-- The cohomology presheaf of the small étale site, evaluated at the identity étale object,
is naturally isomorphic to `Sheaf.functorH`. (Stacks, Tag 03YU) -/
theorem fullAffineEtale_cohomology_base_left (S : Scheme.{u}) [IsAffine S]
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] (p : ℕ) :
    Nonempty (Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
      (CategoryTheory.evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 S))) ≅
      Sheaf.functorH.{w, u} S.smallEtaleTopology p) := by
  let U := Scheme.Etale.mk (𝟙 S)
  let X := (presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  let Z := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal _ _
  let a (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
      (Z ⟶ F) ≃+ F.obj.obj (op U) :=
    ((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u} hU).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  have ha {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (f : F ⟶ G)
      (z : Z ⟶ F) : a G (z ≫ f) = f.hom.app (op U) (a F z) := by
    change (((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u} hU).homEquiv
      _ G (z ≫ f)) (ULift.up 1)) = _
    rw [Adjunction.homEquiv_naturality_right]
    rfl
  let e : coyoneda.obj (op X) ≅ coyoneda.obj (op Z) :=
    NatIso.ofComponents (fun F =>
      ((affineEtaleSectionsEquiv S.smallEtaleTopology U F).toEquiv.trans
        (a F).toEquiv.symm).toIso) (by
        intro F G f
        ext x
        change (a G).symm (affineEtaleSectionsEquiv S.smallEtaleTopology U G (x ≫ f)) =
          (a F).symm (affineEtaleSectionsEquiv S.smallEtaleTopology U F x) ≫ f
        apply (a G).injective
        rw [AddEquiv.apply_symm_apply, ha, AddEquiv.apply_symm_apply,
          affineEtaleSectionsEquiv_naturality])
  let eXZ : op X ≅ op Z := coyoneda.preimageIso e
  exact ⟨(Abelian.extFunctor p).mapIso eXZ⟩

/-- The cohomology presheaf of the full affine étale site, evaluated at the identity affine
object after restriction, is naturally isomorphic to `Sheaf.functorH`.
(Stacks, Tags 03YU, 04HR) -/
theorem fullAffineEtale_cohomology_base_right (S : Scheme.{u}) [IsAffine S]
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] (p : ℕ) :
    Nonempty ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
      Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
        (CategoryTheory.evaluation _ _).obj (op (⟨Scheme.Etale.mk (𝟙 S), ‹IsAffine S›⟩ :
          S.FullAffineEtale)) ≅ Sheaf.functorH.{w, u} S.smallEtaleTopology p) := by
  obtain ⟨e, _⟩ := fullAffineEtale_cohomology_comparison_data S
    (⟨Scheme.Etale.mk (𝟙 S), ‹IsAffine S›⟩ : S.FullAffineEtale)
  obtain ⟨b⟩ := fullAffineEtale_cohomology_base_left S p
  exact ⟨e p ≪≫ b⟩

/-- Cohomology over an affine base is computed compatibly on the small étale site and the full
affine étale site, via `Sheaf.functorH`. (Stacks, Tags 03YU, 04HR) -/
theorem fullAffineEtale_cohomology_base (S : Scheme.{u}) [IsAffine S]
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})] (p : ℕ) :
    Nonempty
      (Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 S))) ≅
        Sheaf.functorH.{w, u} S.smallEtaleTopology p) ∧
    Nonempty
      ((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
        (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op (⟨Scheme.Etale.mk (𝟙 S), ‹IsAffine S›⟩ :
            S.FullAffineEtale)) ≅ Sheaf.functorH.{w, u} S.smallEtaleTopology p) := by
  exact ⟨fullAffineEtale_cohomology_base_left S p,
    fullAffineEtale_cohomology_base_right S p⟩


end AlgebraicGeometry.Scheme
