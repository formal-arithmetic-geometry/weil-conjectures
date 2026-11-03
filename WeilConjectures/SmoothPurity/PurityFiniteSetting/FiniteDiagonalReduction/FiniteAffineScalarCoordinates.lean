/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteAffineSupportedClass
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteOrientationScalarPresentation
public import WeilConjectures.AlgebraicGeometry.SupportedEtaleTensorOrigin.SupportedEtaleTensorOrigin

/-! # Canonical ordinary coordinates for the supported affine scalar maps

Source: blueprint finite reduction of purity, Step 4.
(blueprint: def-pur-affine-scalar-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

/-- Ordinary comparison inverse image followed by intrinsic realization.
Source: finite coefficient site comparison
(blueprint: def-pur-affine-scalar-coordinates). -/
abbrev affineOrdinaryRealization (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory ⋙
    (Scheme.sfIntrinsicDerivedEquivalence T P.Ring).functor

/-- The canonical composite of the native scalar presentation and site scalar mate.
Source: blueprint Step 4, coefficient-unit normalization
(blueprint: def-pur-affine-scalar-coordinates). -/
def affineNativeOrdinaryComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    affineOrdinaryRealization P T ⋙ P.finiteReduction m hm hmn T ≅
      ordinaryScalar (quotient P m hm hmn) T ⋙
        affineOrdinaryRealization (P.finiteReductionSetting m hm) T :=
  (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (ProEtale.SupportedEtaleTensorOrigin.scalarPresentation
      (P.finiteReductionRingHom m hm hmn) T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ProEtale.pbcComparisonReduction T (quotient P m hm hmn)) _ ≪≫
    Functor.associator _ _ _

/-- An ordinary scalar arrow in the canonical intrinsic coordinates.
Source: blueprint Step 4, scalar presentation
(blueprint: def-pur-affine-scalar-coordinates). -/
def affineRealizeScalar (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    {K : Etale.DerivedCategoryModule P.Coefficient T}
    {L : Etale.DerivedCategoryModule (P.finiteReductionSetting m hm).Coefficient T}
    (a : (ordinaryScalar (quotient P m hm hmn) T).obj K ⟶ L) :
    (P.finiteReduction m hm hmn T).obj ((affineOrdinaryRealization P T).obj K) ⟶
      (affineOrdinaryRealization (P.finiteReductionSetting m hm) T).obj L :=
  (affineNativeOrdinaryComparison P m hm hmn T).hom.app K ≫
    (affineOrdinaryRealization (P.finiteReductionSetting m hm) T).map a

/-- The actual derived scalar adjunct of a map of sheaves to scalar restriction.
Source: Stacks 06YY; blueprint Step 4, scalar units
(blueprint: def-pur-affine-scalar-coordinates). -/
def affineScalarSingle {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (a : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj N) :
    (ordinaryScalar φ T).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (_root_.DerivedCategory.singleFunctor _ 0).obj N :=
  ((Etale.purityScalarAdjunction φ T).homEquiv _ _).symm
    ((_root_.DerivedCategory.singleFunctor _ 0).map a ≫
      ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategorySingleFunctor
        0).inv.app N)

/-- Its degree-two shift uses the actual derived scalar shift comparison.
Source: blueprint Step 4, positive Kummer degree
(blueprint: def-pur-affine-scalar-coordinates). -/
def affineScalarShiftedSingle {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (a : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj N) :
    (ordinaryScalar φ T).obj (((_root_.DerivedCategory.singleFunctor _ 0).obj M)⟦(2 : ℤ)⟧) ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj N)⟦(2 : ℤ)⟧ :=
  letI : (ordinaryScalar φ T).CommShift ℤ :=
    (Etale.purityScalarAdjunction φ T).leftAdjointCommShift ℤ
  ((ordinaryScalar φ T).commShiftIso (2 : ℤ)).hom.app _ ≫
    (affineScalarSingle φ T a)⟦(2 : ℤ)⟧'

/-- The supported ordinary constant sheaf at the zero divisor.
Source: blueprint Step 4, supported constant
(blueprint: def-pur-affine-scalar-coordinates). -/
abbrev affineOrdinarySupport (P : PurityFiniteSetting.{u}) (S : Scheme.{u}) :=
  (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
      (Etale.ordinaryFiniteConstant P.Coefficient S)

variable (P : PurityFiniteSetting.{u}) (S : Scheme.{u})
variable [S.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
variable [QuasiCompact (S ↘ Spec (.of P.field.k))]
variable [IsSeparated (S ↘ Spec (.of P.field.k))]

/-- Compact support of the intrinsic coefficient unit, in supported single coordinates.
Source: blueprint Step 4, exact closed direct image
(blueprint: def-pur-affine-scalar-coordinates). -/
def affineSupportedSingleIso :
    (P.smoothCompactSupport (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).obj
      (P.coefficientUnit S) ≅
    (affineOrdinaryRealization P (AffineSpace (ULift.{u} (Fin 1)) S)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj (affineOrdinarySupport P S)) :=
  affineSupportedSourceIso P S ≪≫
    (affineOrdinaryRealization P (AffineSpace (ULift.{u} (Fin 1)) S)).mapIso
      (((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).app
        (Etale.ordinaryFiniteUnit P.Coefficient S)) ≪≫
      (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).singleFunctorCompRightDerivedFunctorIso.app
          (Etale.ordinaryFiniteConstant P.Coefficient S))

omit [IsSeparated (S ↘ Spec (.of P.field.k))] in
/-- The supported orientation is its actual Ext class in the single coordinates.
Source: blueprint Step 4, definition of supportedExactDerivedMap
(blueprint: def-pur-affine-scalar-coordinates).
Proof: unfold the exact closed direct-image comparison and factor realization of
its composite by functoriality. The resulting source comparison is the displayed
single comparison, and the remaining arrow is the Ext realization. -/
theorem affineSupportedSingle_class :
    intrinsicAffineSupportedClass P S =
      (affineSupportedSingleIso P S).hom ≫
        (affineOrdinaryRealization P (AffineSpace (ULift.{u} (Fin 1)) S)).map
          (P.existsUnique_finiteReductionOrientationClass S).choose.hom := by
  simp only [intrinsicAffineSupportedClass, ordinaryAffineSupportedClass,
    affineSupportedSingleIso, Etale.supportedExactDerivedMap,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
