module

public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Sheaf.Paper.DerivedPullbackTensorConstraints
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.AlgebraicallyClosedCoefficients
import Sheaf.Paper.IntegralBraidingScalarExtensionSquare

/-! # Rational braiding and scalar-extension square

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(blueprint: lem-pur-rational-braiding-scalar-extension-square).
-/
@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
open WeilConjectures

namespace WeilConjectures

/-- The rationalized Koszul braiding commutes with the prescribed scalar comparison.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ; the integral
compatibility is `integralBraidingScalarExtensionSquare`, and localization of the
specified maps preserves the square. This includes identity and ramified extensions.
(blueprint: lem-pur-rational-braiding-scalar-extension-square).
-/
theorem rationalBraidingScalarExtensionSquare
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    ∀ (E L : AlgebraicallyClosedCoefficients.Index l Ω) (hEL : E ≤ L),
      ∀ (A B : sfRationalConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W),
        (sfRationalScalarExtension l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime))
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).map
            (pullbackTensorRationalBraiding l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) W A B).hom ≫
          (rationalTensorScalarComparison l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
            (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL) W).hom.app
            (B, A) =
        (rationalTensorScalarComparison l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
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
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L hEL)).obj B)).hom := by
  sorry

end WeilConjectures
