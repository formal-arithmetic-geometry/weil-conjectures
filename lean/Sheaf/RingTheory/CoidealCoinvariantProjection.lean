module

public import Sheaf.RingTheory.CoidealCanonicalTensorIsomorphism

/-! # A coideal retraction projects onto relative Hopf-module coinvariants

Source: Bichon, arXiv:2301.05480v2, Lemma 2.6, specialized to commutative algebras.
(blueprint: lem-sfb-coideal-coinvariant-projection)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace RelativeHopf

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [Bialgebra k H]
variable (A : Subalgebra k H) (S : H →ₐ[k] H)

/-- The formula, retraction identity, and tensored split inclusion of Lemma 2.6.
The submodule R is specified by equality with the dependency's coaction coinvariants.
The pointwise formula specifies p uniquely, using the standard unitor A tensor_A X = X.
Source: Bichon, arXiv:2301.05480v2, Lemma 2.6.
(blueprint: lem-sfb-coideal-coinvariant-projection) -/
def CoinvariantProjectionConclusions
    [hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal]
    (E : H →ₗ[A] A) : Prop :=
  ∀ (X : Type w) [AddCommGroup X] [Module H X] [Module A X] [Module k X]
    [IsScalarTower A H X] [IsScalarTower k A X] [IsScalarTower k H X]
    (α : Coaction k H (Quotient k H A) X)
    (κ : CanonicalTensorIsomorphism k H A S X),
    ∃ R : Submodule A X,
      (R : Set X) = coinvariants k H (Quotient k H A) X (quotientMap k H A 1) α ∧
      ∃ p : X →ₗ[A] R,
        (∀ x : X, R.subtype (p x) =
          TensorProduct.lid A X ((E.rTensor X) (κ.equiv.symm (α.map x)))) ∧
        p.comp R.subtype = LinearMap.id ∧
        Function.Injective (R.subtype.baseChange H) ∧
        (p.baseChange H).comp (R.subtype.baseChange H) = LinearMap.id

/-- An A-linear retraction H to A gives the specified coinvariant projection for every
relative Hopf module and a left inverse after tensoring its inclusion with H.

Source: Bichon, arXiv:2301.05480v2, Lemma 2.6.
(blueprint: lem-sfb-coideal-coinvariant-projection)

Proof plan (the five steps of the node):
1. Use lem-sfb-relative-hopf-module-kernels and the right coideal condition to obtain
   pi(a) = epsilon(a) pi(1) and a(pi(1) tensor x) = pi(1) tensor ax. Thus u(x) =
   pi(1) tensor x is A-linear. Compatibility makes alpha H-linear for the diagonal
   action from lem-sfb-coideal-canonical-tensor-isomorphism. Commutativity makes E
   right A-linear as well; F_Y(h tensor y) = E(h)y is balanced and A-linear.
2. Put beta = kappa_X inverse composed with alpha, T = 1 tensor alpha, and nu =
   1 tensor u. Naturality of the canonical tensor isomorphism gives
   kappa_Z T = (1 tensor alpha) kappa_X. On generators its formula gives
   kappa_Z nu = (Delta_C tensor 1) kappa_X. Precompose with beta; coassociativity
   of alpha and injectivity of kappa_Z imply T beta = nu beta.
3. Apply F_Z to that equality. H-linearity of alpha gives F_Z T = alpha F_X,
   while step 1 gives F_Z nu = u F_X. Consequently q = F_X beta has coinvariant
   values. The canonical inverse and alpha are H-linear for the diagonal action,
   so beta is H-linear and q is A-linear. Restrict its codomain to the coinvariant
   A-submodule supplied by lem-sfb-relative-hopf-module-kernels to obtain p.
4. For a coinvariant r, kappa_X(1 tensor r) = pi(1) tensor r = alpha(r).
   Hence beta(r) = 1 tensor r and q(r) = E(1)r = r, since E restricts to the
   identity on A. This proves p j = 1 and identifies the displayed formula.
5. Tensor p and j with H. Their composite sends h tensor r to h tensor p(j(r)),
   hence is the identity on generators and therefore everywhere. Applying this
   left inverse to an equality proves injectivity, with no flatness assumption. -/
theorem coidealCoinvariantProjection (hA : IsRightCoideal k H A)
    (hSleft : LinearMap.mul' k H ∘ₗ S.toLinearMap.rTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit)
    (hSright : LinearMap.mul' k H ∘ₗ S.toLinearMap.lTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit)
    (E : H →ₗ[A] A) (hE : ∀ a : A, E (a : H) = a) :
    ∃ hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal,
      CoinvariantProjectionConclusions.{u, v, w} k H A S E (hJ := hJ) := by
  sorry

end RelativeHopf
