module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # Faithfully flat quotients of split tori over arbitrary fields

Source: Milne, Algebraic Groups (2017), Theorem 12.9(b),(c), pp.233--234,
and Definition 12.14 and the following paragraph, p.236
(blueprint: lem-sfb-field-split-torus-flat-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An affine finite-type faithfully flat quotient of a split torus is split over the
original field. Rank zero and arbitrary scheme-theoretic kernels are allowed.

Source: Milne, Algebraic Groups (2017), Theorem 12.9(b),(c), pp.233--234;
Definition 12.14 and the following paragraph, p.236; quotient maps as faithfully flat
homomorphisms: Theorems 3.34 and 5.39, Remark 5.42
(blueprint: lem-sfb-field-split-torus-flat-quotient).

Proof:
1. Choose a splitting of T of rank r. Its coordinate Hopf algebra is k[Z^r], by
   lem-sfb-diagonalizable-group-geometric-criteria. Set A = k[Q] and H = k[Z^r].
   The coordinate Hopf structure on A is lem-sfb-affine-group-coordinate-hopf.
   Faithful flatness makes i = q* injective, by
   lem-weil-pbc-faithfully-flat-universally-injective with N = A. Multiplication,
   identity and inverse compatibility of q give compatibility with coproduct,
   counit and antipode. Thus B = i(A) is a unital subalgebra stable under antipode,
   and every coproduct of b in B is a finite sum of tensors of elements of B.
2. Apply the linear map 1 tensor p_n, where p_n extracts the coefficient of e_n,
   to the coproduct of b = sum c_m e_m. The tensor universal property
   def-weil-pbc-module-tensor-product gives c_n e_n in B. If c_n is nonzero,
   division gives e_n in B. Hence B is the span of the monomials it contains.
   This coefficient calculation works over finite and imperfect fields too.
3. The exponents L = {m : e_m in B} form a subgroup of Z^r, using the unit,
   multiplication and antipode. By lem-weil-subgroup-finite-free-abelian-group-free,
   choose a finite basis of L of size t. Sending the basis monomial e_a of k[Z^t]
   to the monomial with exponent given by these basis coordinates defines an
   algebra isomorphism theta : k[Z^t] -> B.
4. Compose theta with i inverse to obtain phi : k[Z^t] -> A. Projecting H onto
   the monomials indexed by L splits i as a linear map, so i tensor i is injective.
   The compatibility in step 1 then shows on each basis monomial that phi preserves
   coproduct, counit and antipode; linearity extends this to all elements.
   The affine-spectrum correspondence def-weil-affine-spectrum yields an isomorphism
   of group schemes Q with D_k(Z^t), hence with the rank-t split torus by
   lem-sfb-diagonalizable-group-geometric-criteria. For r = 0, H = B = k and L = 0,
   so t = 0. No field extension or hypothesis on the kernel has been used. -/
theorem exists_iso_splitTorus_of_faithfullyFlat
    {k : Type u} [Field k] (T Q : Grp (Over (Spec (.of k))))
    (hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    (q : T ⟶ Q) (hq : q.hom.hom.left.appTop.hom.FaithfullyFlat) :
    ∃ t : ℕ, Nonempty (Q ≅ MultiplicativeType.splitTorus k t) := by
  sorry

end AlgebraicGeometry
