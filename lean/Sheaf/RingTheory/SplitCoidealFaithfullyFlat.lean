module

public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Algebra.Tower
import Sheaf.RingTheory.RelativeHopfModuleKernels
import Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism
import Sheaf.RingTheory.CoidealCoinvariantProjection
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # A split commutative coideal inclusion is faithfully flat

Source: Bichon, arXiv:2301.05480v2, Theorem 1.1 and the conditional-expectation
convention before section 2, specialized to commutative algebras.
(blueprint: lem-sfb-split-coideal-faithfully-flat)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace RelativeHopf

/-- A commutative Hopf algebra is faithfully flat over a right coideal subalgebra
that admits a module retraction. The specified inclusion is `algebraMap A B`;
the scalar tower says precisely that this is a k-algebra map. The antipode is
retained as an algebra map with both identities, without requiring any Hopf
structure on A or any finiteness of either algebra.

Source: Bichon, arXiv:2301.05480v2, Theorem 1.1.
(blueprint: lem-sfb-split-coideal-faithfully-flat)

Proof plan (the five steps of the node):
1. Identify A with the image of the injective k-algebra map in B = H.
   Tensoring the injection over the field k is injective, so the tensor-image
   hypothesis is exactly the right coideal condition. Commutativity makes the
   A-linear retraction r an A-bimodule retraction E, and E(1) = 1.
2. Use lem-sfb-relative-hopf-module-kernels to form C = H/HA-plus, induction L,
   and coinvariants R. For X = L(M), lem-sfb-coideal-canonical-tensor-isomorphism
   turns coinvariance of z = sum h_t tensor m_t into
   sum h_t tensor 1 tensor m_t = sum 1 tensor h_t tensor m_t.
   Apply h tensor h' tensor m mapped to E(h)h' tensor m: z = 1 tensor e_M(z),
   where e_M(h tensor m) = E(h)m. This balanced map retracts m mapped to 1 tensor m,
   proving that the unit M to R(L(M)) is bijective.
3. For every relative Hopf module X, lem-sfb-coideal-coinvariant-projection splits
   the coinvariant inclusion j_X and makes 1 tensor j_X injective.
   By lem-sfb-relative-hopf-counit-criterion (1), the counit mu_X is injective;
   part (2), using E, makes it surjective. Thus coinvariants generate X over H.
4. For an injective A-linear f : M to N, lem-sfb-relative-hopf-module-kernels
   makes K = ker L(f) a relative Hopf module. Its coinvariants are the intersection
   with those of L(M), hence have form 1 tensor m. Applying e_N to
   1 tensor f(m) = 0 gives f(m) = 0, so m = 0. Step 3 gives K = 0.
   Tensoring with H therefore preserves injections, which is flatness as in
   def-weil-pbc-flat-ring-map (swap tensor factors for its convention).
5. For a complex M1 to M2 to M3, lem-weil-pbc-tensor-right-exact and step 4
   show exactness is preserved: tensor the quotient by ker(g), then its injection
   into M3. Conversely, exactness after tensoring writes 1 tensor y, for g(y) = 0,
   as a finite sum h_t tensor f(x_t). Applying e_M2 gives
   y = f(sum E(h_t)x_t). The reverse inclusion uses gf = 0.
   Thus tensoring preserves and reflects exactness, exactly
   def-weil-pbc-faithfully-flat-ring-map. -/
theorem splitCoidealFaithfullyFlat
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (B : Type w) [CommRing B] [Bialgebra k B] [Algebra A B] [IsScalarTower k A B]
    (S : B →ₐ[k] B)
    (hSleft : LinearMap.mul' k B ∘ₗ S.toLinearMap.rTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap k B ∘ₗ Coalgebra.counit)
    (hSright : LinearMap.mul' k B ∘ₗ S.toLinearMap.lTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap k B ∘ₗ Coalgebra.counit)
    (hi : Function.Injective (algebraMap A B))
    (hcoideal : ∀ a : A, Coalgebra.comul (R := k) (algebraMap A B a) ∈
      LinearMap.range (TensorProduct.map (IsScalarTower.toAlgHom k A B).toLinearMap
        (LinearMap.id : B →ₗ[k] B)))
    (hsplit : ∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) :
    Module.FaithfullyFlat A B := by
  sorry

end RelativeHopf
