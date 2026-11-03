/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullback
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
import all WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullbackComposition
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-! Transport of the exact and left-derived square comparisons.

(blueprint: lem-pur-pinned-derived-square-transport).

Apply natural-isomorphism extensionality and objectwise extensionality. Expand
leftDerivedFunctorCompNatIso, the composite left-derived comparison, the derived natural
isomorphism and the localized exact square. Use naturality of the final exact-comparison map
twice to move it across the square factors. Cancel inverse comparison factors using the functor
map composition law. Move the remaining vertex isomorphism using naturality and cancel its
inverse. Both sides then have identical components.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

universe w

-- Derived-square transport helper.
/-- Source: categorical transport calculation for the pinned comparison.
(blueprint: lem-pur-pinned-derived-square-transport). -/
theorem derivedSquare_transport
    {C D H V : Type*}
    [Category.{w + 1} C] [Abelian C] [IsGrothendieckAbelian.{w + 1} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{w + 1} D] [Abelian D] [IsGrothendieckAbelian.{w + 1} D]
    [MonoidalCategory D] [MonoidalClosed D] [MonoidalPreadditive D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    [Category.{w + 1} H] [Abelian H] [IsGrothendieckAbelian.{w + 1} H]
    [MonoidalCategory H] [MonoidalClosed H] [MonoidalPreadditive H] [BraidedCategory H]
    [Abelian.HasFunctorialFlatResolution H]
    [Category.{w + 1} V] [Abelian V] [IsGrothendieckAbelian.{w + 1} V]
    [MonoidalCategory V] [MonoidalClosed V] [MonoidalPreadditive V] [BraidedCategory V]
    [Abelian.HasFunctorialFlatResolution V]
    (F : C ⥤ D) (G : D ⥤ V) (J : C ⥤ H) (I : H ⥤ V)
    [F.Additive] [G.Additive] [J.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [J.IsLeftAdjoint] [I.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [J.Monoidal] [I.Monoidal]
    [F.PreservesFlat] [G.PreservesFlat] [J.PreservesFlat] [I.PreservesFlat]
    {G' : DerivedCategory D ⥤ DerivedCategory V}
    {J' : DerivedCategory C ⥤ DerivedCategory H}
    (x : G.mapDerivedCategory ≅ G') (y : J.mapDerivedCategory ≅ J')
    (e : F ⋙ G ≅ J ⋙ I) :
    isoWhiskerRight (J.leftDerivedFunctorIsoMapDerivedCategory ≪≫ y).symm
        I.leftDerivedFunctor ≪≫
      leftDerivedFunctorCompNatIso F G J I e.symm ≪≫
      isoWhiskerLeft F.leftDerivedFunctor (G.leftDerivedFunctorIsoMapDerivedCategory ≪≫ x) =
    (isoWhiskerRight F.leftDerivedFunctorIsoMapDerivedCategory G' ≪≫
      isoWhiskerLeft F.mapDerivedCategory x.symm ≪≫
      mapDerivedCategorySquareIso e ≪≫
      isoWhiskerRight y I.mapDerivedCategory ≪≫
      isoWhiskerLeft J' I.leftDerivedFunctorIsoMapDerivedCategory.symm).symm := by
  apply Iso.ext
  ext K
  simp only [leftDerivedFunctorCompNatIso, leftDerivedFunctorCompIso,
    leftDerivedFunctorNatIso, mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerRight_inv,
    isoWhiskerLeft_hom, isoWhiskerLeft_inv, whiskerRight_app, whiskerLeft_app,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    mapDerivedCategoryNatIso_symm]
  rw [I.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [I.leftDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc]
  rw [← x.hom.naturality]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
