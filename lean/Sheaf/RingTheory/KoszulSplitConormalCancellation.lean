/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import WeilConjectures.RingTheory.KoszulRegularSequence

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.KoszulRegularFlatBaseChange
import WeilConjectures.AlgebraicGeometry.KoszulComplex

/-!
# Koszul-regular cancellation with a split conormal sequence

Source: Stacks Project, Divisors, Tag 068Z, assertion (3), affine ideal form,
and Tag 063G (blueprint: lem-sfb-koszul-split-conormal-cancellation).

The quotient `K ⧸ (J • ⊤ : Submodule R K)` is `K/KJ`. The retraction identity
is stated on the classes of elements of `K`, which generate this quotient.
It specifies the canonical inclusion-induced map, without choosing another map.
Both conormal modules are annihilated by `J`, so an `R`-linear retraction is
exactly an `R/J`-linear one. The canonical conormal sequence is always right
exact, and the retraction identity supplies its left injectivity.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- Cancellation of locally Koszul-regular ideals with a split conormal sequence.
Source: Stacks Project, Tag 068Z(3), affine ideal form, and Tag 063G
(blueprint: lem-sfb-koszul-split-conormal-cancellation).

Proof:
1. Lift a prime of `R/K` containing `J/K` to a prime `p` of `R` containing `J`.
   Choose the common principal neighbourhood supplied by `hlocal`; localizing
   further at `p` identifies the two localized ideals with `K_p` and `J_p`.
2. Tensor the retraction with the residue field of `p`. On pure tensors its
   composite with the inclusion is the identity. Identify the resulting modules
   with `K_p/pK_p` and `J_p/pJ_p` by the fraction formulas. Thus the map between
   these finite dimensional vector spaces is injective; no flatness is needed.
3. Extend a basis of the first space to one of the second, using
   `lem-weil-pbc-vector-space-basis-through-vector`, and clear the finitely many
   denominators to obtain elements `f` of `K` and complementary elements `g` of `J`.
4. Apply `lem-sfb-koszul-generators-from-fibre-basis` to both ideals. On a common
   principal neighbourhood the prefix `f` and concatenation `(f,g)` generate
   their respective ideals and are Koszul-regular. Use localization flatness
   and `lem-sc-koszul-regular-flat-base-change` for this common refinement.
5. The forward implication of `lem-sfb-koszul-prefix-quotient-criterion`
   (Stacks 068M) makes the images of `g` Koszul-regular modulo the prefix ideal;
   they generate the image of `J` there.
6. Multiply the finitely many neighbourhood denominators, and use localization
   commuting with quotients to identify this quotient with `(R/K)_u`, with `u`
   outside the chosen prime. The coefficientwise ring-isomorphism map on Koszul
   complexes transports both regularity and generation. Empty tuples are allowed;
   if `R/K` is the zero ring there are no primes to check.
-/
theorem koszulRegular_quotient_of_split_conormal
    {R : Type u} [CommRing R] (K J : Ideal R) (hKJ : K ≤ J) (hK : K.FG)
    (hlocal : ∀ (p : Ideal R), p.IsPrime → J ≤ p →
      ∃ h : R, h ∉ p ∧
        (∃ (n : ℕ) (f : Fin n → Localization.Away h),
          Ideal.span (Set.range f) = K.map (algebraMap R (Localization.Away h)) ∧
            RingTheory.Sequence.IsKoszulRegular f) ∧
        (∃ (m : ℕ) (g : Fin m → Localization.Away h),
          Ideal.span (Set.range g) = J.map (algebraMap R (Localization.Away h)) ∧
            RingTheory.Sequence.IsKoszulRegular g))
    (hsplit : ∃ r : J.Cotangent →ₗ[R] (K ⧸ (J • ⊤ : Submodule R K)),
      ∀ k : K, r (J.toCotangent ⟨k.1, hKJ k.2⟩) =
        (J • ⊤ : Submodule R K).mkQ k) :
    ∀ (q : Ideal (R ⧸ K)), q.IsPrime → J.map (Ideal.Quotient.mk K) ≤ q →
      ∃ u : R ⧸ K, u ∉ q ∧
        ∃ (n : ℕ) (g : Fin n → Localization.Away u),
          Ideal.span (Set.range g) =
            (J.map (Ideal.Quotient.mk K)).map
              (algebraMap (R ⧸ K) (Localization.Away u)) ∧
            RingTheory.Sequence.IsKoszulRegular g := by
  sorry

end Ideal
