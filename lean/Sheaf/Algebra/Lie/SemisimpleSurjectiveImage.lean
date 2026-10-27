module

public import WeilConjectures.Mathlib.Algebra.Lie.Radical

import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.CartanCriterion

/-! # Surjective images of semisimple Lie algebras

Source: Milne, Algebraic Groups (2017), §22c, printed p.475 (PDF p.487),
final paragraph under The Casimir operator
(blueprint: lem-sfb-semisimple-lie-surjective-image).

Semisimplicity means having no nonzero solvable Lie ideal, expressed by
`LieAlgebra.HasTrivialRadical` as in `def-wf-semisimple-lie-algebra`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace LieAlgebra

/-- A surjective Lie homomorphism between finite-dimensional Lie algebras over a
characteristic-zero field carries a Lie algebra with no nonzero solvable ideal
onto one with the same property.

Source: Milne, Algebraic Groups (2017), §22c, printed p.475 (PDF p.487),
final paragraph under The Casimir operator
(blueprint: lem-sfb-semisimple-lie-surjective-image).

Proof:
1. Put I = ker(q). Bracket preservation makes I an ideal. By
   lem-sfb-semisimple-lie-ideal-complement, choose a complementary ideal J,
   so I intersect J = 0 and I + J = L. This uses characteristic zero,
   finite dimensionality and the trivial solvable radical of L.
2. The restriction q_J : J -> H is injective because I intersect J = 0.
   It is surjective: write a preimage x as i + j, so q(x) = q(j).
   Moreover [I,J] = 0, since every such bracket lies in both ideals.
3. For a solvable ideal A of H, put B = {j in J | q(j) in A}, viewed inside L.
   This is a subspace and an ideal of L: writing x = i + j gives
   [x,b] = [j,b] in J, with q([j,b]) = [q(j),q(b)] in A.
4. Choose n with D^n A = 0. Induction on r shows q(D^r B) is contained in
   D^r A: the successor follows by mapping bracket generators and their
   linear span. Thus q(D^n B) = 0. Since D^n B is contained in J and q_J is
   injective, D^n B = 0. Hence B is a solvable ideal of L and B = 0.
   For a in A, surjectivity of q_J supplies j in B with q(j) = a, so a = 0.
   Thus every solvable ideal of H is zero, equivalently HasTrivialRadical F H
   by hasTrivialRadical_iff_no_solvable_ideals (def-wf-semisimple-lie-algebra).
-/
theorem hasTrivialRadical_of_surjective
    (F : Type u) [Field F] [CharZero F]
    (L : Type v) [LieRing L] [LieAlgebra F L] [Module.Finite F L]
    (H : Type w) [LieRing H] [LieAlgebra F H] [Module.Finite F H]
    (q : L →ₗ⁅F⁆ H) (hq : Function.Surjective q) [HasTrivialRadical F L] :
    HasTrivialRadical F H := by
  sorry

end LieAlgebra
