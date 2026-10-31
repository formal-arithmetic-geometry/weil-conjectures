/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport

/-! # Proper image part of geometric scalar finite evaluation

Source: Stacks 07A6, 0D6E and 0940.
(blueprint: lem-pur-native-support-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of the native support model is compatible with its restriction to
constant coefficients, input reduction and finite image restriction.
Source: Stacks 07A6, 0D6E and 0940; evaluation/scalar-restriction normalization.
(blueprint: lem-pur-native-support-finite-evaluation).
Proof: expand supportModel into its proper and open comparisons. Transpose the
proper square under the finite geometric adjunction. The normalized whole-system
counit and identity-on-sections restriction comparison give equal transposes,
so injectivity of the adjunction bijection proves that square. For the open
square, both comparisons localize the identity on the open and the zero map off
it. Paste these squares, then use naturality of the input reductionEvaluation.
The finiteReductionIso and finiteImageIso factors agree with those used in
supportEvaluation. This proves the equality for every derived input without
asserting faithfulness of evaluation. -/
theorem nativeSupport_finiteEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((supportModel l E c S).hom.app M) ≫
      (constantImageEvaluation l E c n).hom.app ((reduction l E X S).obj M) ≫
      (PurCompactSupport.image (constants l E) c).map
        ((reductionEvaluation l E X S n).hom.app M) ≫
      (positiveImageRestriction l E c (n + 1) (Nat.le_add_left 1 n)).hom.app
        ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
          (Nat.le_add_left 1 n) X)).obj M) =
      (supportEvaluation l E c S n).hom.app M := by sorry

end WeilConjectures.PurStrictScalar
