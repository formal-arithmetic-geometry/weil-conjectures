/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-! # The open site-comparison factor

Source: Stacks Project, Tags 09A6, 09AF and 099R; the factor calculation in
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-compact-support-open-factor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

private theorem inclusion_map {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem inclusion_comp_inv {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusCompIso F G).inv.app K) =
      (Functor.mapDerivedCategoryCompIso F G).inv.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusCompIso F G).app K)).inv =
      ((Functor.mapDerivedCategoryCompIso F G).app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app F G K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem inclusion_nat_inv {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.mapDerivedCategoryPlusNatIso e).inv.app K) =
      (Functor.mapDerivedCategoryNatIso e).inv.app K.obj := by
  change (DerivedCategory.Plus.ι.mapIso
    ((Functor.mapDerivedCategoryPlusNatIso e).app K)).inv =
      ((Functor.mapDerivedCategoryNatIso e).app K.obj).inv
  congr 1
  apply Iso.ext
  exact Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app e K

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_square_conjugate (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {h : Z' ⟶ Z} (sq : CommSq v j' j h) :
    conjugateIsoEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j'))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v))
      (upperStarCompIso (ModuleCat.{u + 1} A) sq.w) =
      squareLowerStarIso (ModuleCat.{u + 1} A) sq := by
  dsimp only [upperStarCompIso, squareLowerStarIso]
  rw [conjugateIsoEquiv_trans _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (v ≫ j)) _,
    conjugateIsoEquiv_trans _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (j' ≫ h)) _,
    conjugateIsoEquiv_upperStarComp, conjugateIsoEquiv_upperStarCongr,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_upperStarComp]
  simp only [Iso.trans_assoc]
  congr 2
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_baseChange_eq (A : Type (u + 1)) [CommRing A]
    {U' U Z' Z : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq v j' j h) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)
      (upperStarCompIso (ModuleCat.{u + 1} A) sq.w).hom).natTrans =
      baseChangeMap (ModuleCat.{u + 1} A) sq := by
  let ah := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
  let av := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v
  let aj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let aj' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j'
  have hc := congrArg Iso.hom (pro_square_conjugate A sq)
  change conjugateEquiv (ah.comp aj') (aj.comp av)
      (upperStarCompIso (ModuleCat.{u + 1} A) sq.w).hom =
      (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom at hc
  have hi := iterated_mateEquiv_conjugateEquiv ah av aj aj'
    (TwoSquare.mk _ _ _ _ (upperStarCompIso (ModuleCat.{u + 1} A) sq.w).hom)
  have hh : mateEquiv ah av
      (TwoSquare.mk _ _ _ _ (upperStarCompIso (ModuleCat.{u + 1} A) sq.w).hom) =
      (mateEquiv aj' aj).symm
        (TwoSquare.mk _ _ _ _ (squareLowerStarIso (ModuleCat.{u + 1} A) sq).hom) := by
    apply (mateEquiv aj' aj).injective
    rw [Equiv.apply_symm_apply]
    apply TwoSquare.ext
    intro M
    exact congr_app (hi.trans hc) M
  exact congrArg TwoSquare.natTrans hh

private theorem derived_symm {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm =
      (Functor.mapDerivedCategoryNatIso e).symm := by
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem pro_extension_iso_eq (A : Type u) [CommRing A] [Finite A]
    {U' U Z' Z : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j h) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    letI := sfFixedOpenExtensionBaseChange_isIso A sq
    ((conjugateIsoEquiv
      ((openImmersionLowerShriekUpperStarAdjunction B j).comp
        (upperStarLowerStarAdjunction B h))
      ((upperStarLowerStarAdjunction B v).comp
        (openImmersionLowerShriekUpperStarAdjunction B j'))).symm
      (@asIso _ _ _ _ (baseChangeMap B sq.toCommSq)
        (isIso_baseChangeMap_of_isPullback B sq))).symm =
      (asIso (sfFixedOpenExtensionBaseChange A sq.toCommSq)).symm := by
  exact congrArg Iso.symm (Iso.ext (congrArg
    (conjugateEquiv
      ((openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).comp
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j'))).symm
    (pro_baseChange_eq (ULift.{u + 1, u} A) sq.toCommSq).symm))

/-- The open factor of the compact-support site-comparison square.
Source: Stacks Project, Tags 03S6 and 09AF; step 5 of
lem-amb-compact-support-site-comparison-open
(blueprint: lem-amb-compact-support-open-factor).

Proof: invert the two extension-by-zero base-change maps and transpose under the
target open adjunction. The unit normalization of the site/open comparison and
of each open base-change mate identifies both transposes with the same composite
of the open unit and the inverse-image comparisons. The latter agree by composite
and cartesian coherence of comparison pullback. The Hom adjunction is injective.
Exactness lets the equation descend termwise to D+. Empty opens and zero objects
are included because this uses only naturality and triangle identities. -/
theorem compactSupportOpenFactor (A : Type u) [CommRing A] [Finite A]
    {U' U Z' Z : Scheme.{u}} {v : U' ⟶ U} {j' : U' ⟶ Z'}
    {j : U ⟶ Z} {h : Z' ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j h)
    (L : DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    letI := Etale.isIso_openImmersionLowerShriekBaseChangeMap
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq
    letI := sfFixedOpenExtensionBaseChange_isIso A sq
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).mapDerivedCategoryPlus.map
        ((properOpenSiteExtensionIso (ULift.{u + 1, u} A) j).hom.app L) ≫
      ((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryPlusNatIso
          (asIso (sfFixedOpenExtensionBaseChange A sq.toCommSq)).symm ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _).hom.app
          ((comparisonUpperStar
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) U).mapDerivedCategoryPlus.obj L) ≫
      (openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j').mapDerivedCategoryPlus.map
          ((fixedComparisonPullbackPlus (ULift.{u + 1, u} A) v).inv.app L) =
    (fixedComparisonPullbackPlus (ULift.{u + 1, u} A) h).inv.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategoryPlus.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z').mapDerivedCategoryPlus.map
          (((Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
            Functor.mapDerivedCategoryPlusNatIso
              (asIso (Etale.openImmersionLowerShriekBaseChangeMap
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq)).symm ≪≫
            Functor.mapDerivedCategoryPlusCompIso _ _).hom.app L) ≫
      (properOpenSiteExtensionIso (ULift.{u + 1, u} A) j').hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) v).mapDerivedCategoryPlus.obj
          L) := by
  let osq : OpenImmersionSquare v j' j h :=
    { toCommSq := sq.toCommSq
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  have he := fixSiteOpenExchange (ULift.{u + 1, u} A) osq L
  apply DerivedCategory.Plus.ι.map_injective
  simp only [properOpenSiteExtensionIso, fixedComparisonPullbackPlus,
    fixSiteOpenComparison, fixSitePullbackComparison,
    Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, inclusion_map, inclusion_comp_inv, inclusion_nat_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app] at he ⊢
  simp only [ordinaryOpenExtensionBaseChangeIso, pro_extension_iso_eq A sq,
    Etale.extensionZeroBaseChangeDerivedPlusIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, inclusion_comp_inv,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, derived_symm, Iso.symm_inv,
    Category.assoc] at he ⊢
  exact he

end AlgebraicGeometry.ProEtale
