module

public import Sheaf.RingTheory.RelativeHopfModuleData
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Quotient coalgebras, induction and kernels for relative Hopf modules

Source: Bichon, arXiv:2301.05480v2, section 2.1 and the exactness discussion after
Theorem 2.1; Stacks Tags 00HD and 09FN for the kernel restriction.
(blueprint: lem-sfb-relative-hopf-module-kernels)
-/

@[expose] public section

set_option autoImplicit false

universe u v w w' z z'

open scoped TensorProduct

namespace RelativeHopf

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [Bialgebra k H]

/-- The conclusions for the canonical quotient coalgebra, after the coideal proof is supplied.
This predicate merely collects the clauses of Bichon section 2.1, including induction on
objects and maps, coinvariants, and restricted kernel coactions. The coalgebra instance is
Mathlib's canonical quotient construction, not a separately chosen structure.
Source: Bichon section 2.1. (blueprint: lem-sfb-relative-hopf-module-kernels) -/
def QuotientConclusions (A : Subalgebra k H)
    [hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal] : Prop :=
  (∀ h : H,
    Coalgebra.comul (R := k) (quotientMap k H A h) =
      TensorProduct.map (quotientMap k H A) (quotientMap k H A) (Coalgebra.comul h) ∧
    Coalgebra.counit (R := k) (quotientMap k H A h) = Coalgebra.counit (R := k) h) ∧
  (∀ h t : H, h • quotientMap k H A t = quotientMap k H A (h * t)) ∧
  (∀ (X : Type z) [AddCommGroup X] [Module k X] [Module H X] [IsScalarTower k H X]
    (α : Coaction k H (Quotient k H A) X),
    ∃ R : Submodule A X, (R : Set X) =
      coinvariants k H (Quotient k H A) X (quotientMap k H A 1) α) ∧
  (∀ (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M],
    ∃! α : Coaction k H (Quotient k H A) (H ⊗[A] M),
      IsInduced k H A M α ∧
      ∀ m : M, (TensorProduct.mk A H M 1) m ∈
        coinvariants k H (Quotient k H A) (H ⊗[A] M) (quotientMap k H A 1) α) ∧
  (∀ (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    (N : Type w') [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
    (α : Coaction k H (Quotient k H A) (H ⊗[A] M))
    (β : Coaction k H (Quotient k H A) (H ⊗[A] N)),
    IsInduced k H A M α → IsInduced k H A N β →
    ∀ f : M →ₗ[A] N,
      IsMorphism k H (Quotient k H A) (H ⊗[A] M) (H ⊗[A] N) α β (f.baseChange H)) ∧
  (∀ (X : Type z) [AddCommGroup X] [Module k X] [Module H X] [IsScalarTower k H X]
    (Y : Type z') [AddCommGroup Y] [Module k Y] [Module H Y] [IsScalarTower k H Y]
    (α : Coaction k H (Quotient k H A) X) (β : Coaction k H (Quotient k H A) Y)
    (f : X →ₗ[H] Y), IsMorphism k H (Quotient k H A) X Y α β f →
    ∃! κ : Coaction k H (Quotient k H A) (LinearMap.ker f),
      IsMorphism k H (Quotient k H A) (LinearMap.ker f) X κ α (LinearMap.ker f).subtype ∧
      ∀ x : LinearMap.ker f,
        x ∈ coinvariants k H (Quotient k H A) (LinearMap.ker f) (quotientMap k H A 1) κ ↔
        (x : X) ∈ coinvariants k H (Quotient k H A) X (quotientMap k H A 1) α)

/-- The augmentation ideal is a coideal; its canonical quotient has the asserted induction,
coinvariant and kernel constructions.

Source: Bichon, arXiv:2301.05480v2, section 2.1, and the discussion after Theorem 2.1.
(blueprint: lem-sfb-relative-hopf-module-kernels)

Proof plan, following the ten steps of the node:
1. For a in A, a - epsilon(a) lies in A-plus. Hence pi(ta) = epsilon(a) pi(t).
   Expand Delta(a) in A tensor H and apply the counit to obtain
   Delta(a) = 1 tensor a + sum (a_i - epsilon(a_i)) tensor t_i.
2. Multiply this formula by Delta(h). For a in A-plus every term lies in
   J tensor H or H tensor J; epsilon(ha) = 0. Finite sums give the coideal assertion.
3. Descend Delta and epsilon through the quotient. Their identities follow on
   representatives from those of H, and multiplication descends because J is an ideal.
4. Coinvariants are a vector subspace. Compatibility and the formula in step 1 give
   alpha(ax) = pi(1) tensor ax, proving A-stability.
5. The displayed induction formula is balanced: expanding Delta(a), replacing pi(ha_i)
   by epsilon(a_i) pi(h), and applying the counit shows beta(ha,m) = beta(h,am).
   The tensor universal property gives its unique linear extension.
6. On h tensor m, coassociativity and the counit follow from H; multiplicativity of
   Delta gives relative compatibility. Extend by linearity to all tensors.
7. Delta(1) = 1 tensor 1 proves unit coinvariance. The unit is the A-linear map
   TensorProduct.mk at 1; the base-change map of an A-linear f is H-linear and its
   coaction square commutes on the generating tensors.
8. For K = ker(f), H-linearity makes K an H-submodule. By field-flatness and flat
   tensor exactness (lem-weil-pbc-module-over-field-flat and lem-weil-pbc-flat-tensor-exact),
   C tensor K embeds in C tensor X with image ker(1 tensor f). The morphism square
   therefore gives the unique restricted linear coaction.
9. Compare coassociativity after C tensor C tensor K embeds in C tensor C tensor X,
   using field-flatness again. The counit equation follows after K embeds in X;
   compatibility follows after C tensor K embeds in C tensor X. These injections
   also prove uniqueness.
10. Apply the injection C tensor K into C tensor X to the coinvariant equation in
    both directions, obtaining R(K) = K intersect R(X).
The tensor manipulations use def-weil-pbc-module-tensor-product and
lem-weil-pbc-algebra-tensor-pushout-universal-property throughout. -/
theorem relativeHopfModuleKernels (A : Subalgebra k H) (hA : IsRightCoideal k H A)
    (S : H →ₐ[k] H)
    (hSleft : LinearMap.mul' k H ∘ₗ S.toLinearMap.rTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit)
    (hSright : LinearMap.mul' k H ∘ₗ S.toLinearMap.lTensor H ∘ₗ Coalgebra.comul =
      Algebra.linearMap k H ∘ₗ Coalgebra.counit) :
    ∃ hJ : ((augmentationIdeal k H A).restrictScalars k).IsCoideal,
      QuotientConclusions.{u, v, w, w', z, z'} k H A (hJ := hJ) := by
  sorry

end RelativeHopf
