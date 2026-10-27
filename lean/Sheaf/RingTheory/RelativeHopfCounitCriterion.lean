module

public import Sheaf.RingTheory.RelativeHopfModuleKernels
import Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism
import Sheaf.RingTheory.CoidealCoinvariantProjection

/-! # The relative Hopf-module counit criterion

Source: Bichon, arXiv:2301.05480v2, Proposition 2.7 and Lemma 2.6,
specialized to commutative algebras, with the explicit retraction argument of the node.
(blueprint: lem-sfb-relative-hopf-counit-criterion)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RelativeHopf

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [Bialgebra k H]
variable (A : Subalgebra k H)

/-- Both counit conclusions, on the canonical quotient coalgebra. The submodule R is
specified by equality with the dependency's coinvariant set. The multiplication map
mu_X, h tensor r to h r, is Mathlib's `LinearMap.liftBaseChange` of the inclusion
`R.subtype`, which is H-linear. The first clause has no
retraction hypothesis; the second assumes only an A-linear retraction and also records
explicit finite generation by coinvariants.
Source: Bichon, Proposition 2.7 and Lemma 2.6, commutative case.
(blueprint: lem-sfb-relative-hopf-counit-criterion) -/
def CounitCriterionConclusions
    [hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal] : Prop :=
  ∀ (X : Type w) [AddCommGroup X] [Module H X] [Module k X]
    [IsScalarTower k H X]
    (α : Coaction k H (Quotient k H A) X),
    ∃ R : Submodule A X,
      (R : Set X) = coinvariants k H (Quotient k H A) X (quotientMap k H A 1) α ∧
      (Function.Injective (R.subtype.liftBaseChange H) ↔
        Function.Injective (R.subtype.baseChange H)) ∧
      (∀ (E : H →ₗ[A] A), (∀ a : A, E (a : H) = a) →
        Function.Surjective (R.subtype.liftBaseChange H) ∧
        ∀ x : X, ∃ (n : ℕ) (h : Fin n → H) (r : Fin n → R),
          x = ∑ i, h i • (r i : X))

/-- The multiplication counit's injectivity is equivalent to injectivity of the tensored
coinvariant inclusion, and an A-linear retraction H to A makes the counit surjective.

Source: Bichon, arXiv:2301.05480v2, Proposition 2.7 and Lemma 2.6; the node's explicit
retraction repair of the tensor-exactness argument, specialized to commutative algebras.
(blueprint: lem-sfb-relative-hopf-counit-criterion)

Proof plan, following the six steps of the node:
1. Use lem-sfb-relative-hopf-module-kernels for the quotient coalgebra, the coinvariant
   A-submodule R and injectivity of alpha, since its counit composite is the identity.
   Tensor balancing gives the displayed multiplication map. Write i = 1 tensor j and
   T = kappa inverse composed with alpha, using
   lem-sfb-coideal-canonical-tensor-isomorphism. Compatibility on h tensor r gives
   alpha mu = kappa i; tensor generation (def-weil-pbc-module-tensor-product) extends
   the equality to all tensors. Hence T mu = i, and T is injective.
2. Since T is injective, T mu = i implies injectivity of mu if and only if i is injective.
   This uses neither a retraction nor flatness.
3. For the surjectivity assertion take the given E, put Y = C tensor X with the diagonal
   action, nu(x) = pi(1) tensor x and delta = alpha - nu. The coideal condition gives
   pi(a) = epsilon(a) pi(1), so nu is A-linear. Compatibility makes alpha H-linear;
   hence delta is A-linear and D = 1 tensor delta is defined.
4. Naturality of kappa gives kappa_Y (1 tensor alpha) = (1 tensor alpha) kappa_X.
   On generators kappa_Y (1 tensor nu) = (Delta_C tensor 1) kappa_X by
   coassociativity of H. Precompose with T; coassociativity of alpha then gives
   kappa_Y D T = 0. Thus D T = 0 because kappa_Y is injective.
5. Define e(h tensor x) = E(h)x and q = e kappa_X inverse. Commutativity and
   A-linearity of E give A-linearity of q. By lem-sfb-coideal-coinvariant-projection,
   q alpha = j p with p : X to R A-linear. Also q nu = 1 since E(1) = 1, so
   q delta = j p - 1. For z = T(x), applying 1 tensor q to Dz = 0 gives
   (1 tensor (j p))z = z. Therefore w = (1 tensor p)z satisfies iw = z.
6. Now alpha(mu(w)) = kappa(iw) = alpha(x); applying the coaction counit gives
   mu(w) = x. Every tensor is a finite sum h_i tensor r_i, by the tensor construction,
   so x = sum h_i r_i. No preservation of arbitrary kernels by tensoring is assumed. -/
theorem relativeHopfCounitCriterion (hA : IsRightCoideal k H A) (S : H →ₐ[k] H)
    (hSleft : LinearMap.mul' k H ∘ₗ S.toLinearMap.rTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit)
    (hSright : LinearMap.mul' k H ∘ₗ S.toLinearMap.lTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit) :
    ∃ hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal,
      CounitCriterionConclusions.{u, v, w} k H A (hJ := hJ) := by
  sorry

end RelativeHopf
