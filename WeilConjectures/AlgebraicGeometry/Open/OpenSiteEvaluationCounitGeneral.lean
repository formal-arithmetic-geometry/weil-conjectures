/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenSiteEvaluationCounit
import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The open evaluation counit normalization for arbitrary coefficient rings

`AlgebraicGeometry.ProEtale.openSiteEvaluationCounit` and the unit normalization it relies on
(`AlgebraicGeometry.ProEtale.openComparison_unit_normalization`) are stated for finite
coefficient rings, but their proofs never use finiteness. This file repeats the argument for an
arbitrary commutative ring `Λ`, giving
`AlgebraicGeometry.ProEtale.comparisonUpperStar_map_openImmersionLowerShriek_counit`: the
comparison `ν^*` carries the counit of `j_! ⊣ j^*` on `D⁺(X_ét, Λ)` to the counit on
`D⁺(X_proét, Λ)`, up to the comparison isomorphisms (2.10) and `j^* ν^* ≅ ν^* j^*`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

set_option backward.defeqAttrib.useBackward true

/-- The canonical pullback comparison, expressed using localization restriction on both
sites. The first factor converts etale restriction to inverse image; the middle factor
is the recorded canonical comparison, and the last converts pro-etale inverse image to
restriction. No independent comparison is chosen.
Source: Stacks Project, Tags 099R and 09AF
(blueprint: lem-sf-open-comparison-unit-normalization). -/
private def restrictionIso (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma restrictionIso_conjugate
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      ((Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) U))
      (restrictionIso A j).hom =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  let B := ModuleCat.{u + 1} A
  let r₀ := Etale.upperStarLowerStarAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s₀ := upperStarLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  change conjugateEquiv (cX.comp s) (r.comp cU)
    (Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).inv _ ≫
      (supportSiteComparisonCoefficientPullbackIso B j).hom ≫
        Functor.whiskerLeft (comparisonUpperStar B X)
          (upperStarIsoOpenImmersionRestriction B j).hom) = _
  rw [← conjugateEquiv_comp (cX.comp s) (r₀.comp cU) (r.comp cU),
    ← conjugateEquiv_comp (cX.comp s) (cX.comp s₀) (r₀.comp cU),
    conjugateEquiv_whiskerLeft s s₀ cX
      (upperStarIsoOpenImmersionRestriction B j).hom,
    conjugateEquiv_whiskerRight r₀ r cU
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv]
  have he : conjugateEquiv r₀ r
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have hp : conjugateEquiv s s₀
      (upperStarIsoOpenImmersionRestriction B j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  rw [he, hp]
  change (𝟙 _ ≫ (conjugateEquiv (cX.comp s₀) (r₀.comp cU))
    (supportSiteComparisonCoefficientPullbackIso B j).hom) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]
  exact congrArg Iso.inv
    ((conjugateIsoEquiv (r₀.comp cU) (cX.comp s₀)).apply_symm_apply
      (supportSiteComparisonCoefficientDirectImageIso B j).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma restriction_directImage_mate
    (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).hom)
      ).natTrans =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  ext M : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  change M.obj.map _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ M.obj.map _)) =
    𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, Scheme.toProEt,
      supportSiteComparisonSiteBaseChangeIso]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem open_unit_normalization (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
        ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app F) ≫
      (restrictionIso A j).hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} A) j).hom.app F) =
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) := by
  let B := ModuleCat.{u + 1} A
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  let e := Etale.openImmersionLowerShriekAdjunction B j
  let d := openImmersionLowerShriekAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let α := TwoSquare.mk _ _ _ _ (restrictionIso A j).hom
  let β := TwoSquare.mk _ _ _ _
    (openImmersionLowerShriekComparisonUpperStarIso B j).inv
  let θ := TwoSquare.mk _ _ _ _ (comparisonLowerStarOpenImmersionRestrictionIso B j).hom
  have ha : mateEquiv cX cU α = θ := by
    apply (mateEquiv s r).injective
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv s r (mateEquiv cX cU α)).natTrans =
      (mateEquiv s r θ).natTrans
    rw [iterated_mateEquiv_conjugateEquiv]
    exact (restrictionIso_conjugate A j).trans
      (restriction_directImage_mate A j).symm
  have hb : mateEquiv cX cU (mateEquiv e d β) = θ := by
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv cX cU (mateEquiv e d β)).natTrans = _
    rw [iterated_mateEquiv_conjugateEquiv]
    exact congrArg Iso.hom
      ((conjugateIsoEquiv (e.comp cX) (cU.comp d)).apply_symm_apply
        (comparisonLowerStarOpenImmersionRestrictionIso B j))
  have h : mateEquiv e d β = α := (mateEquiv cX cU).injective (hb.trans ha.symm)
  have hu := unit_mateEquiv e d β F
  rw [h] at hu
  change (comparisonUpperStar B U).map (e.unit.app F) ≫
    (restrictionIso A j).hom.app _ =
      d.unit.app _ ≫ (openImmersionRestriction B j).map
        ((openImmersionLowerShriekComparisonUpperStarIso B j).inv.app F) at hu
  rw [reassoc_of% hu, ← Functor.map_comp]
  simp
  rfl


set_option backward.isDefEq.respectTransparency false in
private theorem counit_of_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (N : C ⥤ C') (M : D ⥤ D')
    (e : L ⋙ M ≅ N ⋙ L') (a : R ⋙ N ≅ M ⋙ R')
    (hu : ∀ F, N.map (adj.unit.app F) ≫ a.hom.app (L.obj F) ≫
      R'.map (e.hom.app F) = adj'.unit.app (N.obj F)) (B : D) :
    M.map (adj.counit.app B) = e.hom.app (R.obj B) ≫
      L'.map (a.hom.app B) ≫ adj'.counit.app (M.obj B) := by
  rw [← cancel_epi (e.inv.app (R.obj B))]
  simp only [Iso.inv_hom_id_app_assoc]
  apply (adj'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  conv_lhs => rw [← hu (R.obj B)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R'.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := a.hom.naturality (adj.counit.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
  erw [← hn]
  rw [← N.map_comp_assoc, adj.right_triangle_components]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn' := adj'.unit.naturality (a.hom.app B)
  dsimp only [Functor.comp_map, Functor.id_map] at hn'
  erw [← reassoc_of% hn', adj'.right_triangle_components, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem upper_unit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app F) ≫
    (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
    (upperStar (ModuleCat.{u + 1} A) j).map
      ((openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} A) j).hom.app F) =
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) := by
  have h := open_unit_normalization A j F
  change _ ≫ (restrictionIso A j).hom.app _ ≫ _ = _ at h
  simp only [restrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  let B := ModuleCat.{u + 1} A
  have he : (Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F =
      (Etale.openImmersionLowerShriekAdjunction B j).unit.app F ≫
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv.app
        ((Etale.openImmersionLowerShriek B j).obj F) := rfl
  have hp : (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
      ((comparisonUpperStar B U).obj F) =
      (openImmersionLowerShriekAdjunction B j).unit.app
        ((comparisonUpperStar B U).obj F) ≫
      (upperStarIsoOpenImmersionRestriction B j).inv.app _ := rfl
  rw [he, hp, Functor.map_comp]
  rw [← cancel_mono ((upperStarIsoOpenImmersionRestriction B j).hom.app _)]
  dsimp only [B, Functor.comp_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hn := (upperStarIsoOpenImmersionRestriction B j).hom.naturality
    ((openImmersionLowerShriekComparisonUpperStarIso B j).hom.app F)
  dsimp only [B, Functor.comp_obj] at hn
  erw [hn]
  exact h
set_option backward.isDefEq.respectTransparency false in
private theorem derived_unit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    let a := (comparisonUpperStarCompUpperStarIso B j).symm
    let e := openImmersionLowerShriekComparisonUpperStarIso B j
    (comparisonUpperStar B U).mapDerivedCategory.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
          K) ≫
    (Functor.mapDerivedCategorySquareIso a).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj K) ≫
    (upperStar B j).mapDerivedCategory.map
      ((Functor.mapDerivedCategorySquareIso e).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategory.obj K) := by
  dsimp only
  let B := ModuleCat.{u + 1} A
  let e := openImmersionLowerShriekComparisonUpperStarIso B j
  let a := (comparisonUpperStarCompUpperStarIso B j).symm
  have hu : ∀ F,
      (openImmersionLowerShriekUpperStarAdjunction B j).unit.app
          ((comparisonUpperStar B U).obj F) ≫
        (upperStar B j).map (e.inv.app F) =
      (comparisonUpperStar B U).map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app F) ≫
        a.hom.app ((Etale.openImmersionLowerShriek B j).obj F) := by
    intro F
    rw [← upper_unit A j F]
    dsimp only [B, e, a]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (Etale.openImmersionLowerShriekUpperStarAdjunction B j)
    (openImmersionLowerShriekUpperStarAdjunction B j) a e.symm hu K
  have hs : Functor.mapDerivedCategorySquareIso e.symm =
      (Functor.mapDerivedCategorySquareIso e).symm := by
    apply Iso.ext
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
  rw [hs] at h
  dsimp only [B, e, a] at h
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp only [Iso.symm_hom, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
private theorem inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).hom.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).symm.app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

set_option backward.isDefEq.respectTransparency false in
private theorem plus_unit (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let B := ModuleCat.{u + 1} A
    (comparisonUpperStar B U).mapDerivedCategoryPlus.map
      ((Etale.openImmersionLowerShriekUpperStarAdjunction
        B j).mapDerivedCategoryPlusAdjunction.unit.app K) ≫
    (fixedComparisonPullbackPlus A j).hom.app
      ((Etale.openImmersionLowerShriek B j).mapDerivedCategoryPlus.obj K) ≫
    (upperStar B j).mapDerivedCategoryPlus.map
      ((properOpenSiteExtensionIso A j).hom.app K) =
    (openImmersionLowerShriekUpperStarAdjunction B j).mapDerivedCategoryPlusAdjunction.unit.app
      ((comparisonUpperStar B U).mapDerivedCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := derived_unit A j K.obj
  simp only [Functor.map_comp, inclusion_map,
    fixedComparisonPullbackPlus, properOpenSiteExtensionIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Adjunction.mapDerivedCategoryPlusAdjunction,
    Adjunction.map_restrictFullyFaithful_unit_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app] at h ⊢
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simpa only [Category.comp_id, Functor.comp_obj, Functor.mapDerivedCategoryPlus,
    ObjectProperty.lift, DerivedCategory.Plus.ι, ObjectProperty.ι, inducedFunctor,
    Functor.id_obj] using h
set_option backward.isDefEq.respectTransparency false in
/-- Site comparison preserves the evaluation counit of extension by zero.
Source: Stacks Project, Tags 09AF and 099R; step 7 of
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-open-site-evaluation-counit).

Proof: transpose the inverse open comparison under the target open adjunction.
The unit-normalization of the open comparison identifies its transpose with the
pullback comparison followed by the image of the etale open unit. Naturality of
pullback comparison and the etale triangle identity show that the transpose of
the displayed left side has that value. The pro-etale triangle identity gives the
same transpose for the right side. Injectivity of the Hom adjunction proves the
identity. The exact functors and transformations act degreewise on complexes and
preserve quasi-isomorphisms, so this identity descends to the displayed D+ counits.
The calculation also applies to an empty open and to the zero coefficient ring. -/
theorem comparisonUpperStar_map_openImmersionLowerShriek_counit (A : Type (u + 1)) [CommRing A]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] :
    ∀ B : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
          ((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusAdjunction.counit.app B) =
        (properOpenSiteExtensionIso A j).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.obj B) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus A j).hom.app B) ≫
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusAdjunction.counit.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj B) := by
  intro B
  exact counit_of_unit
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusAdjunction
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusAdjunction
    (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus
    (properOpenSiteExtensionIso A j) (fixedComparisonPullbackPlus A j) (plus_unit A j) B

end AlgebraicGeometry.ProEtale
