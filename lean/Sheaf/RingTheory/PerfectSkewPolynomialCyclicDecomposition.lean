module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.SkewPolynomial.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.RingTheory.SkewPolynomialTwoSidedDivision
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Noetherian.Basic

/-! # Cyclic decomposition for the perfect-field Frobenius skew ring

Source: Milne, Algebraic Groups (2017), Proposition 14.51, printed p.297, in the
cyclic-decomposition form used in Proposition 14.52; division algorithms on p.296.
(blueprint: lem-sfb-perfect-skew-polynomial-cyclic-decomposition)

The action is specified by its generator: `hF` fixes it to the p-th power map.
Thus Mathlib's existing `SkewPolynomial k` has multiplication
`(c F^i) (b F^j) = c b^(p^i) F^(i+j)`.
Each quotient below is a quotient of left modules by the span of one element,
which is exactly the principal left ideal A g. No quotient-ring structure is used.
-/

@[expose] public section

universe u v

open scoped DirectSum

namespace SkewPolynomial

/-- A finite left module over the Frobenius skew ring of a perfect field is a
finite direct sum of cyclic left modules, allowing zero cyclic relations.

Source: Milne, Algebraic Groups (2017), Proposition 14.51, printed p.297, with
its erroneous irreducibility restriction omitted, as in the application in 14.52.
(blueprint: lem-sfb-perfect-skew-polynomial-cyclic-decomposition)

Proof plan:
1. By def-weil-field, Frobenius is injective: a^p = b^p implies (a-b)^p = 0,
   hence a = b. It is a ring endomorphism in characteristic p and is surjective
   by hperfect. The action generator is this map by hF, so it is an automorphism.
2. Apply lem-sfb-skew-polynomial-two-sided-division. In a nonzero left ideal,
   choose a nonzero element g of least degree. For f in the ideal, left division
   gives f = q g + r; the remainder belongs to the ideal and has smaller degree
   unless zero. Thus r = 0 and the ideal is A g. The zero ideal is A 0.
3. Choose finitely many generators of M using def-weil-finitely-generated-module,
   giving a surjective left-linear map pi : A^n -> M in row coordinates.
   By lem-sfb-left-principal-finite-submodules, its kernel K is finitely generated.
   Put its generators into the rows of an m by n matrix C, so K = {x C}.
   The map induced by pi identifies A^n / K with M.
4. Apply lem-sfb-two-sided-division-matrix-diagonalization, using degree and the
   two division algorithms, to obtain a diagonal matrix D = U C V with U and V
   invertible. Right multiplication by V is a left-linear automorphism of A^n.
   Since {x U} = A^m, it sends K onto {x D}, and induces an isomorphism of
   the corresponding quotient left modules. No coefficients are commuted.
5. Set g_i = D_ii for i < min(m,n), and g_i = 0 for the remaining coordinates.
   The row module of D consists precisely of tuples whose i-th coordinate is
   in A g_i. Sending a tuple to its coordinate classes has that kernel and is
   surjective: representatives can be chosen for the finitely many coordinates.
   It therefore identifies A^n / {x D} with the finite direct sum of A / A g_i.
   Compose the isomorphisms. Take q = n, including n = 0 and the empty sum;
   a zero diagonal entry gives a free cyclic factor. No irreducibility is used.
-/
theorem exists_frobenius_cyclic_decomposition
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hp : 0 < p)
    [MulSemiringAction (Multiplicative ℕ) k]
    (hF : ∀ c : k, SkewPolynomial.φ c = c ^ p)
    (hperfect : ∀ c : k, ∃ b : k, b ^ p = c)
    (M : Type v) [AddCommGroup M] [Module (SkewPolynomial k) M]
    [Module.Finite (SkewPolynomial k) M] :
    ∃ (q : ℕ) (g : Fin q → SkewPolynomial k),
      Nonempty (M ≃ₗ[SkewPolynomial k]
        ⨁ i : Fin q, SkewPolynomial k ⧸ Submodule.span (SkewPolynomial k) {g i}) := by
  sorry

end SkewPolynomial
