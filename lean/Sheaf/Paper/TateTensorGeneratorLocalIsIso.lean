/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TateTensorGeneratorMap

/-! Pointwise local invertibility of the normalized Tate tensor map.

Source: smooth-purity transport, normalized Tate tower, Step 2.
(blueprint: lem-pur-tate-tensor-generator-local-isiso)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

/-- The compatible root formula gives an isomorphism on every pro-etale section.

Source: current blueprint, sec-smooth-purity/sk-thm-purity-transport, Step 2,
local rank-one argument in the ordinary quotient comparison.
(blueprint: lem-pur-tate-tensor-generator-local-isiso)

Proof: choose the common pro-etale covering with compatible primitive roots.
On each member, scalar coordinates identify the inverse-limit root line with the
coefficient unit, and reduction identifies its ordered tensor with the finite
root tensor. The displayed GeneratorCompatible formula then says that the
section map is the identity between the two rank-one coordinate modules. The
local inverse is multiplication by the inverse coordinate, and compatibility
with restriction makes it the inverse on every pro-etale section. Degree zero
uses the coefficient unit; an empty scheme has the unique section map.
-/
theorem tateTensorQuotient_generator_local_isIso
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (f : (realization T ell n).obj (finiteSheaf T ell n d) ⟶ quotientLine T ell n d)
    (hf : GeneratorCompatible T ell n d f) :
    ∀ W, IsIso (f.val.app W) := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
