/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.SemilinearFieldOperationLifts
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.Paper.ConstantGeometricStalkUnit

/-! # Rational-stage coherence of the normalized constant unit

Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
(blueprint: lem-pur-common-constant-unit-frobenius-rational).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstantPurityFrobenius

/-- The rationalized normalized unit, prior to passage to the common coefficient stage.
Source: constant-comparison proof, Step 2
(blueprint: lem-pur-common-constant-unit-frobenius-rational).
-/
def rationalizedUnit
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    (rationalDerivedPullback l E f).obj
        (constantWeilRationalObject l E D hl Y) ≅
      constantWeilRationalObject l E D hl X :=
  eqToIso ((rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 _) ≪≫
    (sfRationalConstructibleLocalization l E X).mapIso
      (ObjectProperty.isoMk _ (ConstantGeometricStalkUnit.integralUnit l E f))

/-- Rational-stage Frobenius coherence for the normalized constant unit.
Source: constant comparison in the proof of purity/trace equivariance, preceding Step 1.
Proof: identify the two finite quotient maps by the constant-ring composition lemma;
apply the normalized strict Roos unit and its canonical Frobenius comparison at every
quotient; then pass through the derived-limit and rationalization functors. -/
theorem rationalizedUnit_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X₀ Y₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    let f := FrobeniusExchange.fiberMap D f₀
    let K := constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left
    let u := rationalizedUnit D l hl E f
    (podRationalSquarePullbackComponent l E f
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K).hom ≫
        (rationalDerivedPullback l E f).map
          (constantWeilRationalComplex l E D hl Y₀).str.hom ≫ u.hom =
      (sfWeilFrobeniusPullback D l hl X₀ E).map u.hom ≫
        (constantWeilRationalComplex l E D hl X₀).str.hom := by
  sorry

end WeilConjectures.ConstantPurityFrobenius
