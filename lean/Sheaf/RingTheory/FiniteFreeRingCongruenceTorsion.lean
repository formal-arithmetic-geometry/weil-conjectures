module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Sheaf.NumberTheory.AlgebraicIntegerRootUnityCongruence
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-!
# Congruence rigidity for finite-order elements of finite-free integral rings

Source: Milne, Abelian Varieties, Chapter I, Proposition 14.4(b), printed p.62, and
Lemma 14.5, printed p.63, adapted using the faithful left regular representation.
(blueprint: lem-sfb-finite-free-ring-congruence-torsion)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v

/-- A finite-order element of a unital associative ring whose additive group is finite
free over the integers, congruent to one at level at least three, is one.
The positive integers `n` and `r` are represented by natural numbers, and `n • b`
is the sum of `n` copies of `b`. Commutativity and nontriviality are not assumed.

Source: Milne, Abelian Varieties, Chapter I, Proposition 14.4(b), printed p.62, and
Lemma 14.5, printed p.63, with the left regular representation and characteristic-zero
semisimplicity replacing the polarization-specific conclusion.
(blueprint: lem-sfb-finite-free-ring-congruence-torsion)

Proof:
1. Choose a finite integral basis using def-weil-pbc-free-module. Left multiplication
   gives an integral matrix M_x for each x. Associativity gives M_xy = M_x M_y,
   additivity gives M_(x+y) = M_x + M_y, and M_1 = I. The representation is faithful:
   equality on basis vectors gives equality on 1. In rank zero the ring is trivial.
   Otherwise write U = M_u and B = M_b, so U^r = I and U = I + n B.
2. Work over the algebraically closed field of complex numbers, using
   lem-weil-complex-algebraically-closed. The annihilating polynomial p = X^r - 1
   is squarefree: p - (X/r)p' = -1, so a common divisor of p and p' is a unit;
   a square factor h^2 in p would force h to divide both p and p'. The node
   lem-sfb-squarefree-annihilator-invariant-complements supplies invariant complements.
3. For an eigenvector v of U with eigenvalue lambda, U^r v = v gives lambda^r = 1.
   The congruence gives Bv = alpha v, where alpha = (lambda - 1)/n. By
   lem-weil-cayley-hamilton-free-module, B satisfies a monic integer polynomial q
   of positive degree. Map its matrix equation entrywise to the complex numbers;
   q(B)v = q(alpha)v = 0. Since v is nonzero, q(alpha) = 0, so alpha is an
   algebraic integer in the sense of def-weil-algebraic-integer.
4. Apply lem-sfb-algebraic-integer-root-unity-congruence to lambda = 1 + n alpha,
   using n >= 3 and r >= 1, to obtain lambda = 1 for every eigenvalue of U.
5. By lem-sfb-invariant-complements-eigenspace-span, the eigenspaces span the complex
   vector space. Thus U is the identity on their sum and hence U = I.
6. Injectivity of the integer inclusion into the complex numbers gives M_u = M_1
   over the integers. Faithfulness of the left regular representation gives u = 1. -/
theorem eq_one_of_finite_free_ring_congruence
    {R : Type v} [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R]
    (n r : ℕ) (hn : 3 ≤ n) (hr : 1 ≤ r) (u b : R)
    (hpow : u ^ r = 1) (hcongr : u = 1 + n • b) : u = 1 := by
  sorry
