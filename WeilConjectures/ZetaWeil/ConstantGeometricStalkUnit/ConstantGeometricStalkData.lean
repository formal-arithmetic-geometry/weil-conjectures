/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace

import all WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension

/-! # Constructions for constant geometric coefficient stalks

Source: the constant-sheaf clause of `prop-every-iterate-trace`, reviewed expansion
steps 2--8 (blueprint: def-zl-constant-geometric-stalk-constructions).

The existing section, pullback, iteration and scalar-comparison constructions are
re-exported through their original module without changing their definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

attribute [-instance] coefficientComplexModuleDerived pointScalarModuleDerived
  pointCompletedSheafDerived pointScalarAbSheafify pointScalarAbLocallyBijective
  coefficientComplexIntegralAdditive coefficientComplexIntegralLimits
  coefficientComplexIntegralColimits coefficientComplexRationalAdditive
  coefficientComplexRationalLimits coefficientComplexRationalColimits
  coefficientComplexFieldAdditive coefficientComplexFieldLimits coefficientComplexFieldColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The integral stalk in the published full constructible category.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalk (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (constructibleIntegralPullback l E x).obj
    (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)

/-- Iterate the published completed integral Weil comparison.
Source: reviewed expansion steps 3 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralWeilIterate : (r : ℕ) →
    (@constructibleIntegralPullback l _ E _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj
        (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
  | 0 => constantWeilConstructibleIntegralTheta l E D hl Y₀
  | r + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    ((integralPullbackComposition l E).choose
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom).app _ ≪≫
      (constructibleIntegralPullback l E
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (constantWeilConstructibleIntegralTheta l E D hl Y₀) ≪≫
        integralWeilIterate r

/-- Iterate the actual integral point transports, with the specified composition maps.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralTransportIterate (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (r : ℕ) →
    ((pointIntegralFibre D l hl E).obj N).obj ⟶
      ((pointIntegralFibre D l hl E).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)).obj
  | 0 => frobeniusPointTransportIntegral D l hl E N.obj
  | r + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    frobeniusPointTransportIntegral D l hl E N.obj ≫
      integralTransportIterate
        ((constructibleIntegralPullback l E (frobeniusPointIso D).hom).obj N) r ≫
      (pointFibreIntegralAmbient D l E).map
        (((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom).inv.app N).hom

/-- Integral local Frobenius: transport, semilinear return, and the iterated Weil map.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  integralTransportIterate l E D hl (integralStalk l E D hl Y₀ x) r ≫
    (pointFibreIntegralAmbient D l E).map
      ((((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r) x).symm.app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (constructibleIntegralPullback l E f).obj
          (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)) h.symm) ≪≫
        ((integralPullbackComposition l E).choose x
          (localPositivePower (D.geometricFrobenius Y₀).hom r)).app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)).hom).hom ≫
    (pointFibreIntegralAmbient D l E).map
      ((constructibleIntegralPullback l E x).map (integralWeilIterate l E D hl Y₀ r).hom).hom

/-- The actual rational stalk lifted to the section universe is the tensor of its
integral stalk; these are the prescribed object identities and size-descent counit.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalFibreComparison (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (pointFibreModuleLift E).mapDerivedCategory.obj
        (localPointComplex l E D hl Y₀ (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.obj
          ((pointFibreIntegralAmbient D l E).obj (integralStalk l E D hl Y₀ x).obj) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := pointFibreSizeLift_equivalence E
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso
        (localPullbackObjectIso l E x
          (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)) ≪≫
        pointRationalFibreObjIso D l hl E
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
            (integralStalk l E D hl Y₀ x)))) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l hl E (integralStalk l E D hl Y₀ x)))

/-- The integral return and Weil factors, after point transport has finished.
Source: reviewed expansion step 8
(blueprint: def-zl-constant-geometric-stalk-constructions). -/
def integralReturnWeil (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (pointFibreIntegralAmbient D l E).map
      ((((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r) x).symm.app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (constructibleIntegralPullback l E f).obj
          (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)) h.symm) ≪≫
        ((integralPullbackComposition l E).choose x
          (localPositivePower (D.geometricFrobenius Y₀).hom r)).app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)).hom).hom ≫
    (pointFibreIntegralAmbient D l E).map
      ((constructibleIntegralPullback l E x).map (integralWeilIterate l E D hl Y₀ r).hom).hom

/-- The canonical scalar comparison at the output of iterated point transport.
It uses the prescribed object comparisons, followed by the size-descent counit.
Source: reviewed expansion step 8
(blueprint: def-zl-constant-geometric-stalk-constructions). -/
def rationalTransportComparison (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (r : ℕ) :
    (pointFibreModuleLift E).mapDerivedCategory.obj
      ((pointRationalFibre D l hl E).obj
        ((@rationalDerivedPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj
            (localDerivedStalk l E D hl Y₀
              (constantWeilRationalComplex l E D hl Y₀) x))).obj ≅
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.obj
        ((pointFibreIntegralAmbient D l E).obj
          (((@constructibleIntegralPullback l _ E _ _ _ _ _
            (localPositivePower (frobeniusPointIso D).hom r)
            (frobeniusPointPrimeInvertible D l hl)
            (frobeniusPointPrimeInvertible D l hl)).obj
              (integralStalk l E D hl Y₀ x)).obj)) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI := pointFibreSizeLift_equivalence E
  let g := localPositivePower (frobeniusPointIso D).hom r
  let N := integralStalk l E D hl Y₀ x
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso
        ((rationalDerivedPullback l E g).mapIso
          (localPullbackObjectIso l E x
            (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)) ≪≫
          localPullbackObjectIso l E g
            ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj N)) ≪≫
        pointRationalFibreObjIso D l hl E
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
            ((constructibleIntegralPullback l E g).obj N)))) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l hl E
          ((constructibleIntegralPullback l E g).obj N)))

end WeilConjectures.ConstantGeometricStalkUnit
