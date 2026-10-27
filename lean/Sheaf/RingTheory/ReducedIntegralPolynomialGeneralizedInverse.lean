/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Polynomial generalized inverses of reduced integral elements

Source: Stacks Project, Tag 04MI, `varieties.tex`, lemma-integral-closure-ground-field,
reduced integral algebra input; the agent-written polynomial refinement in the DAG.
See also Tags 00J6 and 00JA, `algebra.tex`, lemma-finite-dimensional-algebra and
lemma-product-local.
(blueprint: lem-sfb-reduced-integral-polynomial-generalized-inverse)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsIntegral

/-- An integral element of a reduced commutative algebra over a field has a generalized
inverse given by a polynomial in that element. The algebra may be the zero ring.

Source: the polynomial refinement of the reduced integral algebra input to Stacks
Tag 04MI, `varieties.tex`, lemma-integral-closure-ground-field; compare Tags 00J6
and 00JA, `algebra.tex`, lemma-finite-dimensional-algebra and lemma-product-local.
(blueprint: lem-sfb-reduced-integral-polynomial-generalized-inverse)

Proof (the three steps of the node):
1. By integrality (def-weil-pbc-integral-closure), choose a monic annihilating polynomial
   f of positive degree. A positive-degree witness is available even in the zero ring
   (use X there). Let r be the least index of a nonzero coefficient of f. The field
   hypothesis (def-weil-field) ensures f is nonzero. Shifting coefficients gives
   f = X^r * g with g(0) = a nonzero. Evaluation through the structural algebra map
   respects multiplication (def-weil-polynomial-ring), so x^r * g(x) = 0.
2. If r = 0 then g(x) = 0. Otherwise (x * g(x))^r = 0 by commutativity and the
   preceding equality. Reducedness therefore gives x * g(x) = 0 in both cases.
3. Write g = C a + X * h by separating the constant coefficient. The previous
   equality becomes algebraMap k B a * x + x^2 * h(x) = 0. Set
   q = -C (a inverse) * h. Since a is nonzero in the field k, multiplication by
   its inverse gives x^2 * q(x) = x. These are ring identities, so they also
   apply when x = 0 or the algebra is the zero ring. -/
theorem exists_polynomial_generalized_inverse {k : Type u} {B : Type v}
    [Field k] [CommRing B] [Algebra k B] [IsReduced B] {x : B} (hx : IsIntegral k x) :
    ∃ q : Polynomial k, x ^ 2 * Polynomial.aeval x q = x := by
  sorry

end IsIntegral
