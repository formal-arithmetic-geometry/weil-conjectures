/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.CategoryTheory.HomogeneousPolynomialResolutionData

/-! # Insertion of zero contracts the underlying polynomial deletion complex -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace Profinite.CondensedAction.HomogeneousPolynomial
variable (ell : ℕ) [Fact ell.Prime] (F : Type u) [NormedField F]
  [NormedAlgebra ℚ_[ell] F] (r : ℕ)

/-- Every pinned polynomial model has its underlying inserted-zero contraction.
Source: current blueprint, six-functors direct-images proof paragraph (3), polynomial
resolution input; steps 4-5 of lem-sfb-homogeneous-polynomial-augmented-resolution.
Exact literature reference WANTED.
(blueprint: lem-sfb-homogeneous-polynomial-contraction-existence).

Proof: use the specified monomial coproduct universal property to define h0 by sending
the constant monomial to the identity and every other monomial to zero. Define h n by
extending the finite polynomial substitution insertZero on each monomial coprojection.
These are internal module maps, hence commute with restriction. Coproduct uniqueness
proves the two specified formulas. On the constant monomial h0 is the identity, so
h0 splits the augmentation. In degree zero the two summands send a polynomial f to
f(0) and f(y)-f(0); their sum is f. In positive degree, insertion after the leading
face gives f itself. Each remaining inserted-zero omitted-block term appears twice,
with signs (-1)^j and (-1)^(j+1), so cancels. The given differential formula and
coproduct uniqueness promote these finite polynomial identities to the two required
identities of internal maps. No equivariance of h is asserted or needed. When r=0,
all substitutions fix the sole monomial and the differential alternates zero and
identity, so the same identities hold. -/
theorem contraction_nonempty (P : Model ell F r) :
    Nonempty (Contraction ell F r P) := by sorry

end Profinite.CondensedAction.HomogeneousPolynomial
