/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.AlgebraicGeometry.NativeBaseChange.GeometricProperBaseChange
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.AdicProperAdjunctionRealization
public import WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Localization
public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization

import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.WeilSheaf.Native.NativeDerivedWeilTensorConstructible
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairDerivedForgetComparison
import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
import WeilConjectures.SixFunctors.ProEtale.Adic.ExchangeMate
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTransposition
import WeilConjectures.SixFunctors.WeilFrobeniusAction.WeilFrobeniusActionResolutions
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Canonical comparisons for native proper projection

Source: latest blueprint, fix-lem-tensor-adjunction.proof.md, Step 1, second Hom
bijection; Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, pp. 61--62
(blueprint: def-sf-native-proper-projection-comparison-data).

The arrow is the actual ambient derived counit mate. Its comparisons retain their
sheaf generators, K-flat totalizations and equivariant K-injective computation.

## Main definitions

* `ProperSectionTensor`: the section tensor comparison with generator normalization.
* `properCommonProjection`: the identity-open-normalized common-stage counit mate.
* `properOrdinaryProjection`: the actual ordinary module counit mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.commonStageDerivedPullback WeilConjectures.commonStageDerivedTensor
  AlgebraicGeometry.Scheme.ContinuousRational.modulePull
  AlgebraicGeometry.Scheme.ContinuousRational.derivedPull

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures Opposite
open WeilConjectures.AdicQbarRealization
open AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- Native forgetting in the ordinary section-module coordinates of the realization.
Source: BS 6.8.1, 6.8.14 (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properSectionForget (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X) ⋙
    sectionFunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R

/-- Termwise forgetting and the exact section-module presentation, then localization.
Source: BS 6.8.14 (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properSectionDerived (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :=
  nativeForget k₀ l X ⋙ sectionDerived l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R

/-- Actual termwise section forgetting, with the recorded additive instance.
Source: BS 6.8.14 (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properSectionCochain (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
      CochainComplex (modules l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R) ℤ := by
  letI := R.commutative
  letI := R.sectionsAdditive
  letI : (sectionFunctor l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R).Additive := R.sectionsAdditive
  exact (properSectionForget k₀ l X R).mapHomologicalComplex (.up ℤ)

/-- The canonical cochain computation map of exact section forgetting.
Source: exact-functor localization, Stacks 015F
(blueprint: def-sf-native-proper-projection-comparison-data). -/
def properSectionFactors (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    DerivedCategory.Q ⋙ properSectionDerived k₀ l X R ≅
      properSectionCochain k₀ l X R ⋙ DerivedCategory.Q := by
  letI := R.commutative
  letI := R.sectionsAdditive
  letI : (sectionFunctor l
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R).Additive := R.sectionsAdditive
  letI := R.sectionsLimits
  letI := R.sectionsColimits
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Endofunctor.IsoAlgebra.forget
        (WeilSheaf.frobeniusPullback k₀ l X)).mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (LocallyFiniteAdicRealization.sections l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (properSectionForget k₀ l X R)) (.up ℤ)) _

/-- The actual unbalanced pure tensor followed by the native balanced quotient.
This fixes the section comparison without choosing any scalar automorphism.
Source: Stacks 03EK; native Mod.tensorπ
(blueprint: def-sf-native-proper-projection-comparison-data). -/
def properNativeSheafGenerator (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (M N : ProEtaleWeilSheaf k₀ l X)
    (V : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEtᵒᵖ)
    (x : M.carrier.X.obj.obj V)
    (y : N.carrier.X.obj.obj V) :
    ((properSectionForget k₀ l X R).obj
      ((nativeOpenSheafTensor k₀ l X).obj (M, N))).val.obj V := by
  letI := Sheaf.symmetricCategory
    (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (WeilCoefficients.{u} l)
  exact (Mod.tensorπ M.carrier N.carrier).hom.app V
    ((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (WeilCoefficients.{u} l))
      M.carrier.X N.carrier.X).app V (x ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] y))

/-- Generator in a specified direct-sum total-tensor summand, with no extra sign.
Source: Stacks 012Z, 06YL (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properNativeTotalGenerator (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ)
    (i j n : ℤ) (h : i + j = n)
    (V : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.ProEtᵒᵖ)
    (x : (P.X i).carrier.X.obj.obj V)
    (y : (Q.X j).carrier.X.obj.obj V) :
    ((properSectionForget k₀ l X R).obj
      ((((nativeTensorTotal k₀ l X).obj P).obj Q).X n)).val.obj V :=
  ((properSectionForget k₀ l X R).map
    (nativeOpenTensorInsertion k₀ l X P Q i j n h)).val.app V
      (properNativeSheafGenerator k₀ l X R (P.X i) (Q.X j) V x y)

/-- Canonical tensor comparison in the section presentation. The generator and
representative equations specify its maps on actual equivariant complexes.
Source: BS 6.8.14--6.8.15; Stacks 06YU
(blueprint: def-sf-native-proper-projection-comparison-data). -/
structure ProperSectionTensor (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (R : LocallyFiniteAdicRealization.Realization l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [∀ x : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    (A : At l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber R) where
  cochain : ∀ P Q : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ,
    (properSectionCochain k₀ l X R).obj
      (((nativeTensorTotal k₀ l X).obj P).obj Q) ≅
    (coefficientTotalTensor.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (ring l _ R)).obj
        ((properSectionCochain k₀ l X R).obj P,
          (properSectionCochain k₀ l X R).obj Q)
  generators : ∀ P Q (i j n : ℤ) (h : i + j = n) V x y,
    ((cochain P Q).hom.f n).val.app V
      (properNativeTotalGenerator k₀ l X R P Q i j n h V x y) =
    coefficientTensorGenerator.{u + 1, u + 1, u}
      (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (ring l _ R)
      ((properSectionCochain k₀ l X R).obj P)
      ((properSectionCochain k₀ l X R).obj Q) i j n h V x y
  kflat : ∀ P, NativeIsKFlat k₀ l X P →
    CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (R := ring l _ R)
      ((properSectionCochain k₀ l X R).obj P)
  tensor : nativeDerivedTensor k₀ l X ⋙ properSectionDerived k₀ l X R ≅
    (properSectionDerived k₀ l X R).prod (properSectionDerived k₀ l X R) ⋙ A.closed.tensor
  representative : ∀ P Q (hP : NativeIsKFlat k₀ l X P) (hQ : NativeIsKFlat k₀ l X Q),
    (properSectionDerived k₀ l X R).map (nativeOpenTensorModel k₀ l X P Q hP hQ).hom ≫
      (properSectionFactors k₀ l X R).hom.app
        (((nativeTensorTotal k₀ l X).obj P).obj Q) ≫
      DerivedCategory.Q.map (cochain P Q).hom ≫
      (A.models.iso _ _ _ _ _ (kflat P hP) (kflat Q hQ)).hom =
    tensor.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      A.closed.tensor.map (Prod.mkHom
        ((properSectionFactors k₀ l X R).hom.app P)
        ((properSectionFactors k₀ l X R).hom.app Q))

variable {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (p : Z ⟶ Y) [p.IsOver (Spec (CommRingCat.of k₀))]

/-- Actual cochain-to-right-derived computation map on equivariant complexes.
Source: Stacks 08BJ (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properNativePushUnit (I : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ) :
    DerivedCategory.Q.obj (((lowerStar k₀ l p).mapHomologicalComplex (.up ℤ)).obj I) ⟶
      (lowerStar k₀ l p).rightDerivedFunctor.obj (DerivedCategory.Q.obj I) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (lowerStar k₀ l p).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I) ≫
    (lowerStar k₀ l p).rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso _).hom.app I)

/-- Source of the natural proper projection map, using ambient native tensors.
Source: blueprint Step 1 (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properNativeProjectionSource : WeilComplex k₀ l Z × WeilComplex k₀ l Y ⥤
    DerivedCategory (ProEtaleWeilSheaf k₀ l Y) :=
  (((WeilComplex.objectProperty k₀ l Z).ι ⋙ (lowerStar k₀ l p).rightDerivedFunctor).prod
    (WeilComplex.objectProperty k₀ l Y).ι) ⋙ nativeDerivedTensor k₀ l Y

/-- Target of the natural proper projection map on arbitrary constructible derived inputs.
Source: blueprint Step 1 (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properNativeProjectionTarget : WeilComplex k₀ l Z × WeilComplex k₀ l Y ⥤
    DerivedCategory (ProEtaleWeilSheaf k₀ l Y) :=
  ((WeilComplex.objectProperty k₀ l Z).ι.prod
    ((WeilComplex.objectProperty k₀ l Y).ι ⋙ nativeOpenPull k₀ l p)) ⋙
      nativeDerivedTensor k₀ l Z ⋙ (lowerStar k₀ l p).rightDerivedFunctor

/-- Canonical structure on the existing geometric fiber.
Source: native framework (blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properGeometricOver (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber.Over
      (Spec (.of (AlgebraicClosure k₀))) :=
  ⟨(X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩

attribute [scoped instance] properGeometricOver

/-- Finite type of the existing geometric-fiber structure map, by base change.
Source: Mathlib base-change instances
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properGeometricFiniteType (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    LocallyOfFiniteType ((X ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘
      Spec (.of (AlgebraicClosure k₀))) :=
  inferInstanceAs (LocallyOfFiniteType
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)

attribute [scoped instance] properGeometricFiniteType

/-- Quasi-compactness of the existing geometric-fiber structure map, by base change.
Source: Mathlib base-change instances
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properGeometricQuasiCompact (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    QuasiCompact ((X ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘
      Spec (.of (AlgebraicClosure k₀))) :=
  inferInstanceAs (QuasiCompact
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)

attribute [scoped instance] properGeometricQuasiCompact

/-- The actual geometric base change lies over the geometric point.
Source: geometricFiberMap_comp_geometricFiberToAlgebraicClosure
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properGeometricMapIsOver :
    (NativeBaseChange.geometricMap k₀ p).IsOver (Spec (.of (AlgebraicClosure k₀))) :=
  ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure p
    (comp_over p (Spec (CommRingCat.of k₀)))⟩

attribute [scoped instance] properGeometricMapIsOver

/-- The actual common-stage proper direct image on the geometric fiber.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-native-proper-projection-comparison-data). -/
abbrev properCommonPush (hl : IsUnit (l : AlgebraicClosure k₀))
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)] :=
  geometricCommonStageDirectImage l (PadicAlgCl l) (AlgebraicClosure k₀) hl
    (NativeBaseChange.geometricMap k₀ p)

/-- Proper normalization of the common-stage projection: identity open factor,
then the actual proper counit mate. This is the Rp_! = Rp_* convention.
Source: latest blueprint, fix-prop-projection-formula; BS 6.8.15
(blueprint: def-sf-native-proper-projection-comparison-data). -/
def properCommonProjection (hl : IsUnit (l : AlgebraicClosure k₀))
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (K : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (L : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (commonStageDerivedTensor l (PadicAlgCl l)
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
        ((properCommonPush k₀ l p hl).obj K, L) ⟶
    (properCommonPush k₀ l p hl).obj
      ((commonStageDerivedTensor l (PadicAlgCl l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).obj
          (K, (commonStageDerivedPullback l (PadicAlgCl l)
            (NativeBaseChange.geometricMap k₀ p)).obj L)) :=
  (geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) hl
    (NativeBaseChange.geometricMap k₀ p)).homEquiv _ _
      ((canonicalCommonStagePullbackTensor l (PadicAlgCl l) (NativeBaseChange.geometricMap k₀ p)
        ((properCommonPush k₀ l p hl).obj K) L).hom ≫
      (commonStageDerivedTensor l (PadicAlgCl l)
        (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber).map (Prod.mkHom
          ((geometricCommonStageAdjunction l (PadicAlgCl l) (AlgebraicClosure k₀) hl
            (NativeBaseChange.geometricMap k₀ p)).counit.app K) (𝟙 _)))

/-- The ordinary module projection is the transpose of balanced pullback/tensor
followed by the actual derived counit.
Source: Stacks 07A4, 0B56 (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properOrdinaryProjection
    (R : LocallyFiniteAdicRealization.Realization l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (S : LocallyFiniteAdicRealization.Realization l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    [∀ x : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField x)]
    [∀ y : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      Invertible (l : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber.residueField y)]
    (A : At l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R)
    (B : At l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)
    (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)
    (C : Proper.TensorComparison l (NativeBaseChange.geometricMap k₀ p) R S O A B)
    (M : DerivedCategory (modules l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R))
    (N : DerivedCategory (modules l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S)) :
    B.closed.tensor.obj
      ((ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).obj M, N) ⟶
    (ContinuousRational.DirectImage.derivedPush
      (NativeBaseChange.geometricMap k₀ p) O.coefficient).obj
      (A.closed.tensor.obj (M,
        (ContinuousRational.derivedPull
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).obj N)) :=
  O.adjunction.homEquiv _ _
    (C.tensor.hom.app
      ((ContinuousRational.DirectImage.derivedPush
        (NativeBaseChange.geometricMap k₀ p) O.coefficient).obj M, N) ≫
      A.closed.tensor.map (Prod.mkHom (O.adjunction.counit.app M) (𝟙 _)))

/-- Termwise form of the specified ordinary sheaf pushforward comparison.
Source: Stacks 08BJ (blueprint: def-sf-native-proper-projection-comparison-data). -/
def properPushSheafCochain
    (R : LocallyFiniteAdicRealization.Realization l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (S : LocallyFiniteAdicRealization.Realization l
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (O : Proper.Operations l (NativeBaseChange.geometricMap k₀ p) R S)
    (b : lowerStar k₀ l p ⋙ properSectionForget k₀ l Y S ≅
      properSectionForget k₀ l Z R ⋙
        ContinuousRational.DirectImage.modulePush
          (NativeBaseChange.geometricMap k₀ p) O.coefficient) :
    (lowerStar k₀ l p).mapHomologicalComplex (.up ℤ) ⋙ properSectionCochain k₀ l Y S ≅
      properSectionCochain k₀ l Z R ⋙
        (ContinuousRational.DirectImage.modulePush
          (NativeBaseChange.geometricMap k₀ p) O.coefficient).mapHomologicalComplex (.up ℤ) := by
  letI := R.commutative
  letI := R.sectionsAdditive
  letI := S.commutative
  letI : (sectionFunctor l
    (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber R).Additive := R.sectionsAdditive
  letI : (sectionFunctor l
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber S).Additive := S.sectionsAdditive
  exact Functor.mapHomologicalComplexCompIso b (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (properSectionForget k₀ l Z R ⋙
        ContinuousRational.DirectImage.modulePush
          (NativeBaseChange.geometricMap k₀ p) O.coefficient)) (.up ℤ)).symm

end AlgebraicGeometry.ProEtaleWeilSheaf
