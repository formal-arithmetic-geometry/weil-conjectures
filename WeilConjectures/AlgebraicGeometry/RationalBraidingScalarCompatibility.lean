/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRationalDerivedOperations
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorConstraints
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.AlgebraicallyClosedCoefficients
import WeilConjectures.AlgebraicGeometry.LocalizedTensorBraidingNaturality
import WeilConjectures.AlgebraicGeometry.IntegralBraidingNaturality
import WeilConjectures.AlgebraicGeometry.RationalBraidingScalarSquare

/-!
# Naturality and scalar compatibility of rational tensor braiding

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(blueprint: lem-pur-rational-braiding-scalar-compatibility).
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open WeilConjectures

namespace WeilConjectures


/-- The prescribed rational Koszul braiding is natural and commutes with scalar extension.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(blueprint: lem-pur-rational-braiding-scalar-compatibility).
Proof: First, coherent reduction identifies the integral braiding with the signed
Koszul swap, so its naturality gives the displayed equation on integral arrows.
The rational tensor and braiding are the prescribed localizations; bilinearity and
localization balancing extend the equation to arbitrary rational arrows.  For a
finite coefficient inclusion `E ≤ L`, the scalar extension and tensor comparison
are the prescribed rationalizations of their integral counterparts.  On integral
representatives the scalar square is the integral signed-swap square, and
localization preserves it.  The argument includes identity and ramified
extensions and uses no finite-field, perfectness, or torsion hypothesis.
(blueprint: lem-pur-rational-braiding-scalar-compatibility). -/
theorem rationalBraidingScalarCompatibility
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (hEL : E ≤ L),
      (∀ (A A' B B' : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W)
          (a : A ⟶ A') (b : B ⟶ B'),
        (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W).map
            (Prod.mkHom a b) ≫
          (pullbackTensorRationalBraiding l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W A' B').hom =
        (pullbackTensorRationalBraiding l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W A B).hom ≫
          (rationalDerivedTensor l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W).map
            (Prod.mkHom b a)) ∧
      (∀ (A B : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W),
        (sfRationalScalarExtension l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).map
            (pullbackTensorRationalBraiding l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W A B).hom ≫
          (rationalTensorScalarComparison
            l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W).hom.app
            (B, A) =
        (rationalTensorScalarComparison
            l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W).hom.app
            (A, B) ≫
          (pullbackTensorRationalBraiding l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W
            ((sfRationalScalarExtension l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).obj A)
            ((sfRationalScalarExtension l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
              (Nat.Prime.ne_zero (Fact.out : l.Prime))
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).obj B)).hom) := by
  intro E L hEL
  constructor
  · intro A A' B B' a b
    exact localizedTensorBraiding_naturality
      l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W
      (by
        intro M M' N N' f g
        exact pullbackTensorIntegralBraiding_naturality l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W
          M M' N N' f g) A A' B B' a b
  · exact rationalBraidingScalarExtensionSquare l Ω W E L hEL

end WeilConjectures
