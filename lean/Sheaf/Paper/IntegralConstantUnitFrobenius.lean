/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.SemilinearFieldOperationLifts
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.ConstantGeometricStalkUnit

/-! Integral normalized-unit Frobenius square used by the rational-stage comparison.
Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

/-- The integral square component through the normalized pullback compositors.
Source: constant comparison proof, finite and completed integral stages.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/
def integralSquarePullbackComponent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (h : gX ≫ f = f ≫ gY)
    (K : sfIntegralConstructibleCategory l E Y) :
    (constructibleIntegralPullback l E gX).obj
        ((constructibleIntegralPullback l E f).obj K) ≅
      (constructibleIntegralPullback l E f).obj
        ((constructibleIntegralPullback l E gY).obj K) :=
  (pullbackTensorIntegralComposition l E f gX).symm.app K ≪≫
    eqToIso (congrArg (fun m : X ⟶ Y ↦
      (constructibleIntegralPullback l E m).obj K) h) ≪≫
    (pullbackTensorIntegralComposition l E gY f).app K

/-- The normalized completed constant unit commutes with the geometric Frobenius square
at the integral coefficient stage.
Source: constant comparison proof, finite quotient composition followed by the normalized
Roos unit and its canonical integral Frobenius comparison.
(blueprint: lem-pur-common-constant-unit-frobenius-integral).
-/
theorem integralUnit_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    let f := FrobeniusExchange.fiberMap D f₀
    let K := constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
    let u := ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f)
    (integralSquarePullbackComponent l E f
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (constructibleIntegralPullback l E f).map
          (constantWeilConstructibleIntegralTheta l E D hl Y₀).hom ≫ u.hom =
      (constructibleIntegralPullback l E (D.geometricFrobenius X₀).hom).map u.hom ≫
        (constantWeilConstructibleIntegralTheta l E D hl X₀).hom := by
  sorry


end WeilConjectures.ConstantPurityFrobenius
