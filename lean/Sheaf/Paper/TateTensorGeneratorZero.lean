/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorGeneratorCompatibility

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-zero)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The coefficient-unit case of the normalized quotient comparison.

Source: smooth-purity transport, Step 2, degree-zero coefficient multiplication.
(blueprint: lem-pur-tate-tensor-generator-zero)

Proof: identify the comparison pullback of the constant finite coefficient module
with the constant pro-etale coefficient module, using the unit constraint of the
comparison functor. Its additive sheafification, with scalars extended along
`scalars`, is the unit module of the finite coefficient sheaf: the map sends a
constant section a to `scalars(a)`. Identify scalar extension of the completed
coefficient unit with the finite coefficient unit by multiplication s tensor r
maps to s times projection(r). Compose the former map with the inverse of the
latter unit isomorphism. On a constant a its value is scalars(a) tensor 1, as
required. All root tuples have empty index set, so their compatibility hypothesis
is vacuous. The construction uses no invertibility assumption and also applies
to the empty scheme. -/
theorem tateTensorQuotient_generator_zero
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime] (n : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n 0) ⟶ quotientLine T ell n 0,
      GeneratorCompatible T ell n 0 f := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
