/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.ScalarPullbackMateInvertible
public import WeilConjectures.AlgebraicGeometry.EtaleChartComparison.EtaleChartComparisonIsos
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleAmbientDirectImageComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.CategoryTheory.UnboundedExactTower.UnboundedExactAdjunctionSquare
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ExactRightDerivedAdjointKFlatRepresentative

/-! # Normalized scalar/pullback comparisons and bounded-below ambient mate

Source: lem-fix-compact-support-coefficient-change, pullback compatibility and final
site transport; det-prop-scalar-six-direct-image, Finite rings; Stacks 06YY, 09A6.
(blueprint: lem-sfb-scalar-site-comparison-normalized-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrdinaryScalarSite

/-- The published scalar extension left adjoint to actual exact derived restriction.
Source: Stacks 06YY; def-sp-coefficient-scalar-representatives
(blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
abbrev scalar {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) := CoefficientScalarRepresentatives.extension J a

/-- The forward etale comparison is the inverse of the published scalar mate,
transported through the specified exact geometric comparisons.
Source: Stacks 06YY, 07A4
(blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
def etaleIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalar Y.smallEtaleTopology a ⋙
        (Etale.upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        scalar X.smallEtaleTopology a :=
  Functor.isoWhiskerLeft _
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm ≪≫
    (@asIso _ _ _ _
      (((mateEquiv
        (CoefficientScalarRepresentatives.adjunction Y.smallEtaleTopology a)
        (CoefficientScalarRepresentatives.adjunction X.smallEtaleTopology a)).symm
          (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom)).natTrans)
      (CoefficientScalarRepresentatives.etaleScalarPullbackMate_isIso a f)).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _

/-- The forward pro-etale comparison is the inverse of the published scalar mate,
transported through the specified exact geometric comparisons.
Source: Stacks 06YY, 07A4
(blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
def proEtaleIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalar (Scheme.ProEt.topology Y) a ⋙
        (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        scalar (Scheme.ProEt.topology X) a :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm ≪≫
    (@asIso _ _ _ _
      (((mateEquiv
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology Y) a)
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology X) a)).symm
          (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom)).natTrans)
      (CoefficientScalarRepresentatives.proEtaleScalarPullbackMate_isIso a f)).symm ≪≫
    Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _

/-- Ordinary etale scalar extension commutes with pullback by the uniqueness of
left adjoints to the sectionwise restriction/direct-image composite.
Source: Stacks 03EL (blueprint: lem-sfb-scalar-site-comparison-normalized-data). -/
def etaleSheafIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CoefficientScalarRepresentatives.ordinaryExtension Y.smallEtaleTopology a ⋙
        Etale.upperStar (ModuleCat.{u + 1} B) f ≅
      Etale.upperStar (ModuleCat.{u + 1} A) f ⋙
        CoefficientScalarRepresentatives.ordinaryExtension X.smallEtaleTopology a :=
  ((Sheaf.adjunction Y.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} a)).comp
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)).leftAdjointUniq
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (Sheaf.adjunction X.smallEtaleTopology
        (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} a)))

private theorem ordinary_restriction_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom)).natTrans =
        𝟙 _ := by
  apply (mateEquiv (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology a)
    (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology a)).injective
  change (mateEquiv (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology a)
    (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology a)
    (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [Etale.upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq,
    Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, TwoSquare.mk]
  erw [Equiv.apply_symm_apply]
  ext M ⟨U⟩ x
  exact congrArg (fun t ↦ ModuleCat.Hom.hom t x)
    ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} a).right_triangle_components
      (M.obj.obj (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U)))).symm

private theorem ordinary_scalar_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((mateEquiv (CoefficientScalarRepresentatives.ordinaryAdjunction Y.smallEtaleTopology a)
      (CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom)).natTrans =
        (etaleSheafIso a f).inv := by
  let δ := (mateEquiv
    (CoefficientScalarRepresentatives.ordinaryAdjunction Y.smallEtaleTopology a)
    (CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom)
  apply (conjugateEquiv
    ((CoefficientScalarRepresentatives.ordinaryAdjunction Y.smallEtaleTopology a).comp
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f))
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).comp
      (CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology a))).injective
  have h := iterated_mateEquiv_conjugateEquiv
    (CoefficientScalarRepresentatives.ordinaryAdjunction Y.smallEtaleTopology a)
    (CoefficientScalarRepresentatives.ordinaryAdjunction X.smallEtaleTopology a)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) δ
  dsimp only [δ] at h
  rw [Equiv.apply_symm_apply, ordinary_restriction_mate] at h
  rw [← h]
  simp only [etaleSheafIso, Adjunction.leftAdjointUniq,
    CoefficientScalarRepresentatives.ordinaryAdjunction, conjugateIsoEquiv_symm_apply_hom,
    Iso.symm_inv, Iso.refl_hom]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.ProEtale.OrdinaryScalarSite
