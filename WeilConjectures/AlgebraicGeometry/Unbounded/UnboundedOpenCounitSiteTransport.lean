/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenComparisonUnitNormalization
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence

/-!
# Actual unbounded open adjunctions and site-comparison counits

Source: Stacks Project, Tags 03DI, 03DJ and 09AF; blueprint
sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md,
Locality paragraph (blueprint: lem-sp-unbounded-open-counit-site-transport).

The sheaf adjunctions are the specified Kan-extension/sheafification adjunctions.
`Adjunction.mapHomologicalComplex` gives their actual degreewise units and counits,
`Adjunction.mapHomotopyCategory` descends them to homotopy categories, and
`Adjunction.mapDerivedCategoryAdjunction` gives their unbounded derived adjunctions.
Its normalization on localized representatives is recorded in the imported
`Adjunction.mapDerivedCategoryAdjunction_unit_app_Qh_obj` and counit counterpart.
Thus no independent adjunction or comparison is selected here.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory

-- Transposing both sides reduces counit compatibility to the two right triangles.
end CategoryTheory

namespace CategoryTheory.Functor

-- Uniqueness of right derived transformations compares the two inclusion paths.

private lemma counit_of_hom_transport {C D C' D' : Type*}
    [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {S : D ⥤ C} {L' : C' ⥤ D'} {S' : D' ⥤ C'}
    (a : L ⊣ S) (b : L' ⊣ S') (P : C ⥤ C') (Q : D ⥤ D')
    (e : L ⋙ Q ≅ P ⋙ L') (r : S ⋙ P ≅ Q ⋙ S')
    (hh : ∀ F H (f : L.obj F ⟶ H),
      b.homEquiv _ _ (e.inv.app F ≫ Q.map f) =
        P.map (a.homEquiv F H f) ≫ r.hom.app H) (H : D) :
    e.hom.app (S.obj H) ≫ L'.map (r.hom.app H) ≫ b.counit.app (Q.obj H) =
      Q.map (a.counit.app H) := by
  apply (cancel_epi (e.inv.app (S.obj H))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply (b.homEquiv _ _).injective
  erw [hh]
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  erw [← b.unit.naturality_assoc, b.right_triangle_components, Category.comp_id]
  rw [← P.map_comp_assoc, a.right_triangle_components, P.map_id, Category.id_comp]
  rfl

private lemma normalized_identity_compat {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ C) [F.Additive] (ε : F ≅ 𝟭 C)
    (E : F.rightDerivedFunctor ≅ 𝟭 (_root_.DerivedCategory C))
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      F.rightDerivedFunctorUnit.app K ≫ E.hom.app (_root_.DerivedCategory.Qh.obj K) =
        _root_.DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ε.hom (.up ℤ)).app K))
    (K : _root_.DerivedCategory.Plus C) :
    F.rightDerivedFunctorPlusCompatibility.hom.app K ≫ E.hom.app K.obj =
      _root_.DerivedCategory.Plus.ι.map
        ((rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso C).hom.app K) := by
  have he : F.rightDerivedFunctorPlusCompatibility.hom ≫
      whiskerLeft _root_.DerivedCategory.Plus.ι E.hom =
      whiskerRight (rightDerivedFunctorPlusNatIso ε ≪≫ rightDerivedFunctorPlusIdIso C).hom
        _root_.DerivedCategory.Plus.ι := by
    apply rightDerived_ext (F.rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι)
      F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
    ext M
    have hc : _root_.DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app M) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app
          (_root_.DerivedCategory.Plus.Qh.obj M) =
        F.rightDerivedFunctorUnit.app M.obj := by
      simpa [rightDerivedFunctorPlusCompatibility, rightDerivedFunctorPlusιUnit,
        ιRightDerivedFunctorUnit] using
        NatTrans.congr_app (rightDerivedNatTrans_fac
          (F.rightDerivedFunctorPlus ⋙ _root_.DerivedCategory.Plus.ι)
          (_root_.DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
          F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
          (HomotopyCategory.Plus.quasiIso C) (𝟙 _)) M
    dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
      rightDerivedFunctorPlusιUnit]
    erw [← Category.assoc, hc, h, ← map_comp]
    erw [rightDerivedFunctorPlusUnit_app_comp_natIso_trans_idIso_hom_app]
    rfl
  exact NatTrans.congr_app he K

-- The exact-derived identity map has the same unit normalization.

private lemma normalized_identity_exact {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [HasKInjectiveResolutions C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (ε : F ≅ 𝟭 C) (K : HomotopyCategory C (.up ℤ)) :
    F.rightDerivedFunctorUnit.app K ≫
      (F.rightDerivedFunctorIsoMapDerivedCategory ≪≫ mapDerivedCategoryNatIso ε ≪≫
        mapDerivedCategoryIdIso C).hom.app (_root_.DerivedCategory.Qh.obj K) =
      _root_.DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory ε.hom (.up ℤ)).app K) := by
  have hi := NatTrans.congr_app (congrArg Iso.hom (mapDerivedCategoryIdIso_factorsh C)) K
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    isoWhiskerRight_hom, whiskerRight_app, rightUnitor_hom_app, leftUnitor_hom_app,
    mapHomotopyCategoryIdIso_hom_app_eq_id] at hi
  erw [_root_.DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id] at hi
  have hf := NatTrans.congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
  simp only [NatTrans.comp_app, whiskerLeft_app] at hf
  simp only [Iso.trans_hom, NatTrans.comp_app, ← Category.assoc]
  erw [hf, Category.assoc, hi, mapDerivedCategoryNatIso_fach_assoc,
    Iso.inv_hom_id_app_assoc, Category.comp_id]

/-- The canonical open comparisons preserve the actual units, evaluation counits, and
adjunction Hom bijections on all unbounded complexes. The last clause identifies the
restriction with the fixed compact-support comparison for the identity proper factor.
The Hom identity implies the stated transport on any full subcategories where the
comparison functors are equivalences: their full faithfulness identifies the Hom sets,
and essential surjectivity covers every pro-etale object and recovers the actual counit.

Source: blueprint Locality paragraph; Stacks Project, Tags 03DI, 03DJ and 09AF
(blueprint: lem-sp-unbounded-open-counit-site-transport).

Proof:
1. Use the specified sheaf adjunctions and the sheaf unit normalization. Cancel the
   extension comparison to put that equation in mate form.
2. The exact-derived mate theorem localizes this equation for the specified actual
   derived adjunctions. Cancel the inverse extension comparison to obtain the unit clause.
3. Expand the adjunction Hom maps using the units. The mate equation and naturality of
   the restriction comparison give the Hom clause. Applying it to the etale counit and
   using both right triangle identities proves the counit clause.
4. For the identity direct image, the bounded-below derived base-change identity law
   identifies its specified comparison with the canonical identity isomorphisms. Their
   compatibility with inclusion into the unbounded category follows by uniqueness of
   right derived transformations, comparing their units on homotopy representatives.
5. Expand the fixed compact-support comparison for j followed by the identity. Substitute
   the identity direct-image formula. Naturality and inverse cancellation remove the
   inclusion comparisons and direct-image identities, leaving the inverse extension
   comparison on K.obj. -/
theorem unboundedOpenCounitSiteTransport (R : Type (u + 1)) [CommRing R]
    [Finite R] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.map
          ((unboundedOpenEtaleAdjunction R j).unit.app F) ≫
        (unboundedOpenRestrictionComparison R j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj F) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
          ((unboundedOpenExtensionComparison R j).hom.app F) =
      (unboundedOpenProEtaleAdjunction R j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj F)) ∧
    (∀ (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (unboundedOpenExtensionComparison R j).hom.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj H) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
          ((unboundedOpenRestrictionComparison R j).hom.app H) ≫
        (unboundedOpenProEtaleAdjunction R j).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj H) =
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((unboundedOpenEtaleAdjunction R j).counit.app H)) ∧
    (∀ (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)))
      (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
      (f : (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj F
        ⟶ H),
      (unboundedOpenProEtaleAdjunction R j).homEquiv _ _
          ((unboundedOpenExtensionComparison R j).inv.app F ≫
            (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map f) =
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.map
            ((unboundedOpenEtaleAdjunction R j).homEquiv F H f) ≫
          (unboundedOpenRestrictionComparison R j).hom.app H) ∧
    (∀ (K : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} R))),
      (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj
            ((comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory.obj K.obj)) ≫
        (fixedCompactSupportComparisonIso R (Compactification.ofIsOpenImmersion j)).hom.app K ≫
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
          ((Etale.rightDerivedLowerStarIdIso R X).hom.app
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj K.obj)) =
        (unboundedOpenExtensionComparison R j).inv.app K.obj) := by
  let B := ModuleCat.{u + 1} R
  let a := Etale.openImmersionLowerShriekAdjunction B j
  let b := openImmersionLowerShriekAdjunction B j
  let e := openImmersionLowerShriekComparisonUpperStarIso B j
  let r := openComparisonRestrictionIso R j
  have hsheaf (F : Sheaf U.smallEtaleTopology B) :
      b.unit.app ((comparisonUpperStar B U).obj F) ≫
        (openImmersionRestriction B j).map (e.inv.app F) =
      (comparisonUpperStar B U).map (a.unit.app F) ≫
        r.hom.app ((Etale.openImmersionLowerShriek B j).obj F) := by
    dsimp only [B, a, b, e, r]
    rw [← (openComparison_unit_normalization R j).2 F]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
    erw [(openImmersionRestriction (ModuleCat.{u + 1} R) j).map_id, Category.comp_id]
  have hm := Adjunction.mapDerivedCategoryAdjunction_mate a b r e.symm hsheaf
  have he : (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (unboundedOpenExtensionComparison R j).inv := by
    simp only [unboundedOpenExtensionComparison, e, Functor.mapDerivedCategorySquareIso,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Category.assoc]
    rfl
  have hu (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology B)) :
      (comparisonUpperStar B U).mapDerivedCategory.map
          ((unboundedOpenEtaleAdjunction R j).unit.app F) ≫
        (unboundedOpenRestrictionComparison R j).hom.app
          ((Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj F) ≫
        (openImmersionRestriction B j).mapDerivedCategory.map
          ((unboundedOpenExtensionComparison R j).hom.app F) =
      (unboundedOpenProEtaleAdjunction R j).unit.app
        ((comparisonUpperStar B U).mapDerivedCategory.obj F) := by
    have h := hm F
    rw [he] at h
    change (unboundedOpenProEtaleAdjunction R j).unit.app _ ≫
      (openImmersionRestriction B j).mapDerivedCategory.map
        ((unboundedOpenExtensionComparison R j).inv.app F) =
      (comparisonUpperStar B U).mapDerivedCategory.map
        ((unboundedOpenEtaleAdjunction R j).unit.app F) ≫
          (unboundedOpenRestrictionComparison R j).hom.app _ at h
    rw [← reassoc_of% h, ← Functor.map_comp, Iso.inv_hom_id_app]
    erw [(openImmersionRestriction B j).mapDerivedCategory.map_id]
    exact Category.comp_id _
  have hh (F : _root_.DerivedCategory (Sheaf U.smallEtaleTopology B))
      (H : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B))
      (f : (Etale.openImmersionLowerShriek B j).mapDerivedCategory.obj F ⟶ H) :
      (unboundedOpenProEtaleAdjunction R j).homEquiv _ _
          ((unboundedOpenExtensionComparison R j).inv.app F ≫
            (comparisonUpperStar B X).mapDerivedCategory.map f) =
        (comparisonUpperStar B U).mapDerivedCategory.map
            ((unboundedOpenEtaleAdjunction R j).homEquiv F H f) ≫
          (unboundedOpenRestrictionComparison R j).hom.app H := by
    have h := hm F
    rw [he] at h
    change (unboundedOpenProEtaleAdjunction R j).unit.app _ ≫
      (openImmersionRestriction B j).mapDerivedCategory.map
        ((unboundedOpenExtensionComparison R j).inv.app F) =
      (comparisonUpperStar B U).mapDerivedCategory.map
        ((unboundedOpenEtaleAdjunction R j).unit.app F) ≫
          (unboundedOpenRestrictionComparison R j).hom.app _ at h
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    rw [← Category.assoc, h, Category.assoc]
    congr 1
    exact ((unboundedOpenRestrictionComparison R j).hom.naturality f).symm
  refine ⟨hu, ?_, hh, ?_⟩
  · exact counit_of_hom_transport (unboundedOpenEtaleAdjunction R j)
      (unboundedOpenProEtaleAdjunction R j) _ _
      (unboundedOpenExtensionComparison R j) (unboundedOpenRestrictionComparison R j) hh
  · intro K
    let T := comparisonUpperStar B X
    let L := Etale.openImmersionLowerShriek B j
    let L' := openImmersionLowerShriek B j
    let M := L.mapDerivedCategoryPlus.obj K
    let c := L.mapDerivedCategoryPlusCompatibility.app K
    let d := (unboundedOpenExtensionComparison R j).app K.obj
    let E := Etale.rightDerivedLowerStarIdIso R X
    let E' := rightDerivedLowerStarId B X
    have hdi : (fixedDirectImageComparisonIso R (𝟙 X)).inv.app M =
        E'.hom.app (T.mapDerivedCategory.obj M.obj) ≫
          T.mapDerivedCategory.map (E.inv.app M.obj) := by
      have hf : (fixedDirectImageComparisonIso R (𝟙 X)).app M =
          T.mapDerivedCategory.mapIso (E.app M.obj) ≪≫
            (E'.app (T.mapDerivedCategory.obj M.obj)).symm :=
        Iso.ext (fixedDirectImageComparisonIso_id_hom R X M)
      exact congrArg Iso.inv hf
    dsimp only [fixedCompactSupportComparisonIso, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Compactification.ofIsOpenImmersion]
    simp only [Functor.mapDerivedCategoryNatIso_symm, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, Category.id_comp, Category.comp_id, Category.assoc]
    have hd :
        ((comparisonUpperStar B U).mapDerivedCategoryCompIso L').inv.app K.obj ≫
          (Functor.mapDerivedCategoryNatIso
            (openImmersionLowerShriekComparisonUpperStarIso B j)).inv.app K.obj ≫
          (L.mapDerivedCategoryCompIso T).hom.app K.obj = d.inv := by
      simp only [d, unboundedOpenExtensionComparison, Functor.mapDerivedCategorySquareIso,
        Iso.app_inv, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv, Category.assoc]
      rfl
    erw [hd]
    change E'.inv.app _ ≫
      (lowerStar B (𝟙 X)).rightDerivedFunctor.map d.inv ≫
      (lowerStar B (𝟙 X)).rightDerivedFunctor.map (T.mapDerivedCategory.map c.inv) ≫
      (fixedDirectImageComparisonIso R (𝟙 X)).inv.app M ≫
      T.mapDerivedCategory.map ((Etale.lowerStar B (𝟙 X)).rightDerivedFunctor.map c.hom) ≫
      T.mapDerivedCategory.map (E.hom.app (L.mapDerivedCategory.obj K.obj)) = d.inv
    rw [hdi]
    simp only [Category.assoc]
    erw [← E'.inv.naturality_assoc, ← E'.inv.naturality_assoc,
      E'.inv_hom_id_app_assoc]
    simp only [Functor.id_map]
    simp only [← T.mapDerivedCategory.map_comp]
    erw [← E.inv.naturality_assoc]
    simp only [Functor.id_map]
    erw [E.inv_hom_id_app, Category.comp_id, c.inv_hom_id,
      T.mapDerivedCategory.map_id, Category.comp_id]

/-- The specified canonical restriction comparison, applied degreewise and localized.
Its sheaf-level input is the recorded pullback comparison in restriction form.
Source: Stacks Project, Tags 03DI, 03DJ and 09AF
(blueprint: lem-sp-unbounded-open-counit-site-transport). -/
noncomputable def unboundedOpenRestrictionComparison (R : Type (u + 1)) [CommRing R]
    [Finite R] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ⋙
        (openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (openComparisonRestrictionIso R j)

-- Identify the specified mate, including both bounded-below inclusion comparisons.

/-- The specified canonical open extension comparison, applied degreewise and localized.
The composition identifications are the canonical derived-functor identifications.
Source: Stacks Project, Tags 03DI, 03DJ and 09AF
(blueprint: lem-sp-unbounded-open-counit-site-transport). -/
noncomputable def unboundedOpenExtensionComparison (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) j)

/-- The actual pro-etale evaluation adjunction on unbounded derived categories. The
specified sheaf counit evaluates each factorization summand and is zero on an empty sum;
the exact-adjunction construction localizes this same map.
Source: Stacks Project, Tags 03DI, 03DJ and 09AF
(blueprint: lem-sp-unbounded-open-counit-site-transport). -/
noncomputable def unboundedOpenProEtaleAdjunction (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory ⊣
      (openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).mapDerivedCategoryAdjunction

/-- The actual etale evaluation adjunction on unbounded derived categories. The existing
exact-adjunction construction localizes the specified degreewise unit and counit.
Source: Stacks Project, Tags 03DI, 03DJ and 09AF
(blueprint: lem-sp-unbounded-open-counit-site-transport). -/
noncomputable def unboundedOpenEtaleAdjunction (R : Type (u + 1)) [CommRing R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory ⊣
      (Etale.openImmersionRestriction (ModuleCat.{u + 1} R) j).mapDerivedCategory :=
  (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} R) j).mapDerivedCategoryAdjunction

private lemma fixedDirectImageComparisonIso_id_hom (R : Type (u + 1)) [CommRing R]
    [Finite R] (X : Scheme.{u})
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (fixedDirectImageComparisonIso R (𝟙 X)).hom.app K =
      (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.map
        ((Etale.rightDerivedLowerStarIdIso R X).hom.app K.obj) ≫
      (rightDerivedLowerStarId (ModuleCat.{u + 1} R) X).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory.obj K.obj) := by
  let B := ModuleCat.{u + 1} R
  let G := Etale.lowerStar B (𝟙 X)
  let G' := lowerStar B (𝟙 X)
  let T := comparisonUpperStar B X
  let E := Etale.rightDerivedLowerStarIdIso R X
  let E' := rightDerivedLowerStarId B X
  let I := Functor.rightDerivedFunctorPlusNatIso (Etale.lowerStarId B X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _
  let I' := Functor.rightDerivedFunctorPlusNatIso (lowerStarId B X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso _
  have hE (M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology B)) :
      G.rightDerivedFunctorPlusCompatibility.hom.app M ≫ E.hom.app M.obj =
        _root_.DerivedCategory.Plus.ι.map (I.hom.app M) :=
    Functor.normalized_identity_compat G (Etale.lowerStarId B X) E
      (Functor.normalized_identity_exact G (Etale.lowerStarId B X)) M
  have hE' (M : _root_.DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) B)) :
      G'.rightDerivedFunctorPlusCompatibility.hom.app M ≫ E'.hom.app M.obj =
        _root_.DerivedCategory.Plus.ι.map (I'.hom.app M) := by
    apply Functor.normalized_identity_compat G' (lowerStarId B X) E' _ M
    intro N
    change G'.rightDerivedFunctorUnit.app N ≫
      (Functor.rightDerivedFunctorNatTrans (lowerStarId B X).hom).app
        (_root_.DerivedCategory.Qh.obj N) ≫
      (Functor.rightDerivedFunctorIdIso _).hom.app (_root_.DerivedCategory.Qh.obj N) = _
    rw [Functor.rightDerivedFunctorNatTrans_app_assoc,
      Functor.rightDerivedFunctorIdIso_fac_app]
    erw [Category.comp_id]
  have hm : (fixedComparisonDirectImageMatePlus R (𝟙 X)).app K =
      T.mapDerivedCategoryPlus.map (I.hom.app K) ≫
        I'.inv.app (T.mapDerivedCategoryPlus.obj K) :=
    Functor.rightDerivedFunctorPlusBaseChange_id (Etale.lowerStarId B X)
      (lowerStarId B X) _ (lowerStarComparisonUpperStarBaseChange_app_id B X) K
  apply (cancel_mono (E'.hom.app (T.mapDerivedCategory.obj K.obj))).1
  dsimp only [B, G, G', T, E, E', Etale.rightDerivedLowerStarPlus] at *
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  simp only [fixedDirectImageComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, asIso_hom, Category.assoc]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map]
  erw [NatTrans.naturality]
  simp only [Functor.id_map]
  erw [reassoc_of% (hE' (T.mapDerivedCategoryPlus.obj K))]
  erw [hm]
  have hcancel :
      _root_.DerivedCategory.Plus.ι.map
          (T.mapDerivedCategoryPlus.map (I.hom.app K) ≫
            I'.inv.app (T.mapDerivedCategoryPlus.obj K)) ≫
        _root_.DerivedCategory.Plus.ι.map
          (I'.hom.app (T.mapDerivedCategoryPlus.obj K)) =
      _root_.DerivedCategory.Plus.ι.map (T.mapDerivedCategoryPlus.map (I.hom.app K)) := by
    rw [← _root_.DerivedCategory.Plus.ι.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  erw [reassoc_of% hcancel]
  erw [T.mapDerivedCategoryPlusCompatibility.hom.naturality]
  simp only [Functor.comp_map]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← hE K]
  erw [← T.mapDerivedCategory.map_comp, Iso.inv_hom_id_app_assoc]

-- Identify the specified mate, including both bounded-below inclusion comparisons.

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
