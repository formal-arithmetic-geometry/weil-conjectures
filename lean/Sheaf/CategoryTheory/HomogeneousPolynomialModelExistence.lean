/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.HomogeneousPolynomialResolutionData

/-! # Existence of the equivariant polynomial deletion complex -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace Profinite.CondensedAction.HomogeneousPolynomial
variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- The pinned equivariant polynomial complex exists over every normed coefficient field.
Source: current blueprint, six-functors direct-images proof paragraph (3), polynomial
resolution input; steps 1-3 of lem-sfb-homogeneous-polynomial-augmented-resolution.
Exact literature reference WANTED.
(blueprint: lem-sfb-homogeneous-polynomial-model-existence).

Proof: on each profinite parameter S take finite polynomials over C(S,F) in the
(n+1)r variables. Coefficient restriction defines the presheaf. Finite products glue
because a finite union of finite monomial supports is finite. For a surjection T → S,
descend each of the finitely many coefficients in the equalizer for C(-,F); uniqueness
is coefficientwise. Thus these are module sheaves. The internal/sectionwise module
equivalence identifies each with the coproduct of regular modules indexed by monomials:
a family of maps extends uniquely by finite linear combinations. Diagonal substitution
by y_(a,i)-g_i is coefficient-linear, natural in S, and satisfies T_g T_t=T_(g+t).
Coordinate deletion commutes with translation. Its alternating sum squares to zero:
for a<b the two omissions carry signs (-1)^(a+b-1) and (-1)^(a+b) and cancel.
Include constants in degree zero and extend the complex by zero in negative degrees.
Translation fixes constants, and the degree-zero differential kills them, so this is
the required equivariant augmentation. These constructions give every field of Model.
For r=0 the index has just the constant monomial, and the same finite calculations apply.
No completeness of F or choice of a witness of an unproved existence result is used. -/
theorem model_nonempty : Nonempty (Model ell F r) := by sorry

end Profinite.CondensedAction.HomogeneousPolynomial
