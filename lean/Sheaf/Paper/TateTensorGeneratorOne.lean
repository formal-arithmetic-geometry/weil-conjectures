/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorGeneratorCompatibility

/-! Tensor-degree construction of the integral Tate quotient comparison.

Source: smooth-purity transport, normalized Tate tower, Step 1.
(blueprint: lem-pur-tate-tensor-generator-one)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The first root line admits the normalized quotient comparison.

Source: smooth-purity transport, Step 2, quotient of the inverse-limit root line.
(blueprint: lem-pur-tate-tensor-generator-one)

Proof: on a common pro-etale primitive-root tower cover identify the inverse-limit
root module with its completed coefficient unit, and identify the level-n roots
module with the finite coefficient unit using the level-n root of that same tower.
The root projection is then coefficient reduction. Thus its scalar extension is
an isomorphism, and the square with the actual root projection commutes. This
isomorphism is independent of the tower basis: replacing the basis multiplies
both coordinates by the same compatible unit. It consequently glues, retaining
the projection formula. The finite etale root module extended to the finite
coefficient ring and pulled to the pro-etale site is the same finite root module,
by the root site comparison and scalar-extension universal property. Compose its
realization with the inverse of the normalized reduction isomorphism. Finally
insert the completed tensor unit on the left, since `integralLine 1` is the unit
tensored with the root line. On the generator a,z with compatible lift x this
sends a,z to scalars(a) tensor (1 tensor x); the projection square proves the
formula for every x, not just a primitive root. Empty-scheme sections satisfy the
same identity by uniqueness. -/
theorem tateTensorQuotient_generator_one
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n : ℕ) :
    ∃ f : (realization T ell n).obj (finiteSheaf T ell n 1) ⟶ quotientLine T ell n 1,
      GeneratorCompatible T ell n 1 f := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
