module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
import Sheaf.RingTheory.ParameterRootAlgebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-! # Fields obtained by adjoining roots of p-independent elements

Source: Stacks Project, More on Algebra, Tag 09II,
`proposition-epp-essentially-finite-type`, p-base preparation paragraph.
(blueprint: lem-sfb-p-independent-root-quotient-field)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra.ParameterRoot

/-- Finite simultaneous root quotients of a p-independent tuple are fields, with the
specified bounded monomial basis, and their p-power-height powers lie in the coefficient field.
For the empty tuple the coefficient inclusion is an isomorphism.

Source: Stacks Project, More on Algebra, Tag 09II,
`proposition-epp-essentially-finite-type`, p-base preparation paragraph.
(blueprint: lem-sfb-p-independent-root-quotient-field)

Proof: Set q = p^n. By `lem-sfb-simultaneous-root-algebra-api`, the quotient has the
basis of root monomials with each exponent below q. The zero-exponent basis vector is 1,
so the coefficient map is injective and the quotient is nontrivial. The same API's
`emptyEquiv` identifies the empty-tuple quotient with k. Frobenius, as in
`def-weil-ring-frobenius`, applied to a basis expansion z = sum_E a_E t^E gives
z^q = sum_E a_E^q b^E, the image of a scalar c in k. This includes z = 0.
By `lem-sfb-p-independent-higher-power-monomials`, the b^E for E_i < q are independent
over the q-th-power subfield. Thus if z is nonzero, a nonzero expansion coefficient
forces c to be nonzero: otherwise independence makes all a_E^q, and hence all a_E,
zero. The element c^(-1) z^(q-1) is then an inverse of z. Commutativity and
nontriviality give the field criterion of `def-weil-field`. -/
theorem isField_of_pIndependent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : ℕ) (b : Fin r → k)
    (hb : LinearIndependent (frobenius k p).fieldRange
      (fun e : Fin r → Fin p ↦ ∏ i, b i ^ (e i).val))
    (n : ℕ) (hn : 1 ≤ n) :
    IsField (Algebra.pthRootAlgebra (p ^ n) r k b) ∧
      (∃ B : Module.Basis (Fin r → Fin (p ^ n)) k
          (Algebra.pthRootAlgebra (p ^ n) r k b),
        ∀ e, B e = ∏ i,
          (Ideal.Quotient.mk _ (MvPolynomial.X i) :
            Algebra.pthRootAlgebra (p ^ n) r k b) ^ (e i).val) ∧
      (∀ z : Algebra.pthRootAlgebra (p ^ n) r k b, ∃ a : k,
        algebraMap k (Algebra.pthRootAlgebra (p ^ n) r k b) a = z ^ (p ^ n)) ∧
      (r = 0 → Function.Bijective
        (algebraMap k (Algebra.pthRootAlgebra (p ^ n) r k b))) := by
  sorry

end Algebra.ParameterRoot
