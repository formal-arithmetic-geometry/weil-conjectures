/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Algebra.LocallyFreeCharpoly
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Module.LinearMap.Prod

/-! # Characteristic polynomials on locally free direct sums

Source: Stacks Project, Tag 09XI, proof of (3)⇒(1), the characteristic-polynomial
factorization for eB and (1-e)B (blueprint: lem-weil-pbc-charpoly-locally-free-direct-sum).
-/

@[expose] public section

universe u v₁ v₂

namespace Algebra

/-- The product cover trivializes the direct sum, and characteristic polynomials multiply.
Source: Stacks Project, Tag 09XI, proof of (3)⇒(1)
(blueprint: lem-weil-pbc-charpoly-locally-free-direct-sum).
The binary direct sum is represented by the product module. The cover is enumerated using
`finProdFinEquiv`, so it contains precisely every product of the original cover elements.

Proof:
1. Choose coefficients expressing 1 as a linear combination of each cover. Multiply the
expressions: the pairwise products generate the unit ideal.
2. Over A localized at f₁ i * f₂ j, each factor is invertible. Use
`lem-weil-pbc-localization-away-tensor-iso` and `lem-weil-pbc-free-base-change-tower` to
extend the two local bases to that ring (the maps are supplied by
`def-weil-pbc-module-localization-away`).
3. Tensor product commutes with the binary direct sum, intertwining the scalar-extended
endomorphism with the product of the two scalar-extended endomorphisms. Their bases give a
basis of size n₁+n₂. The localization-tensor isomorphism transports it to the localized
product module. This proves the asserted local freeness on the product cover.
4. By `def-weil-pbc-charpoly-locally-free`, all three characteristic polynomials restrict
to the corresponding free characteristic polynomials on this cover. Apply
`lem-weil-pbc-charpoly-direct-sum-free` there to obtain the product identity locally.
5. Each coefficient of the difference vanishes in every cover localization. Apply
`lem-weil-pbc-localized-span-eq-zero` to each coefficient, using step 1, to get the equality
in A[T]. -/
theorem locallyFreeCharpoly_prodMap
    {A : Type u} {M₁ : Type v₁} {M₂ : Type v₂} [CommRing A]
    [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
    {n₁ n₂ r₁ r₂ : ℕ} (f₁ : Fin r₁ → A) (f₂ : Fin r₂ → A)
    (hgen₁ : Ideal.span (Set.range f₁) = ⊤)
    (hgen₂ : Ideal.span (Set.range f₂) = ⊤)
    (hfree₁ : ∀ i : Fin r₁,
      ∃ _e : Module.Basis (Fin n₁) (Localization.Away (f₁ i))
        (LocalizedModule.Away (f₁ i) M₁), True)
    (hfree₂ : ∀ j : Fin r₂,
      ∃ _e : Module.Basis (Fin n₂) (Localization.Away (f₂ j))
        (LocalizedModule.Away (f₂ j) M₂), True)
    (φ₁ : M₁ →ₗ[A] M₁) (φ₂ : M₂ →ₗ[A] M₂) :
    let g : Fin (r₁ * r₂) → A := fun k ↦
      f₁ (finProdFinEquiv.symm k).1 * f₂ (finProdFinEquiv.symm k).2;
    ∃ (hggen : Ideal.span (Set.range g) = ⊤)
      (hgfree : ∀ k : Fin (r₁ * r₂),
        ∃ _e : Module.Basis (Fin (n₁ + n₂)) (Localization.Away (g k))
          (LocalizedModule.Away (g k) (M₁ × M₂)), True),
      locallyFreeCharpoly g hggen hgfree (φ₁.prodMap φ₂) =
        locallyFreeCharpoly f₁ hgen₁ hfree₁ φ₁ * locallyFreeCharpoly f₂ hgen₂ hfree₂ φ₂ := by
  sorry

end Algebra
