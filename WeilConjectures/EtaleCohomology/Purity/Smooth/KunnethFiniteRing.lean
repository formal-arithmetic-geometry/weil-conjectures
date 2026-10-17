/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary

/-!
# Ordinary Künneth at a finite coefficient ring

The purity chapter uses the Künneth formula of `thm-kun-0f1p` at the coefficient rings
`A = 𝒪_E/ϖ_E^n` for `E/ℚ_ℓ` finite and `ℓ` invertible on the base field `k`. This file records
it in that form: for `X`, `Y` of finite type over a separably closed field `k` and a finite ring
`Λ` whose exponent is invertible in `k`, the exterior product
`RΓ(X, K) ⊗ᴸ RΓ(Y, L) ⟶ RΓ(X ×_k Y, K ⊠ᴸ L)` is an isomorphism; the case of the rings
`𝒪 ⧸ (ϖ ^ n)` killed by a power of a prime `ℓ` invertible in `k` is spelled out separately.

## Main results

- `AlgebraicGeometry.Etale.nonempty_iso_kunneth_pullback_of_isSepClosed`
  (`lem-pur-ordinary-kunneth-finite-ring`): the Künneth isomorphism for `X ×_k Y`.
- `AlgebraicGeometry.Etale.nonempty_iso_kunneth_quotient_pow`: the case `Λ = 𝒪 ⧸ (ϖ ^ n)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- A ring `Λ` killed by a power of a natural number `ℓ` which is nonzero in a field `k` has
invertible exponent on `Spec k`. -/
theorem HasInvertibleExponent.spec_of_pow_eq_zero (Λ : Type*) [CommRing Λ] {k : Type u}
    [Field k] {ℓ m : ℕ} (hℓ : (ℓ : k) ≠ 0) (hΛ : ((ℓ ^ m : ℕ) : Λ) = 0) :
    HasInvertibleExponent Λ (Spec (.of k)) := by
  have h : ((ℓ ^ m : ℕ) : k) ≠ 0 := by simpa using pow_ne_zero m hℓ
  refine ⟨ℓ ^ m, Nat.pos_of_ne_zero fun h0 ↦ h (by simp [h0]), hΛ, ?_⟩
  simpa using (IsUnit.mk0 _ h).map (Scheme.ΓSpecIso (.of k)).inv.hom

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Blueprint `lem-pur-ordinary-kunneth-finite-ring`: ordinary Künneth at a finite coefficient
ring.

Let `k` be a separably closed field (e.g. the algebraically closed field of
`def-weil-finite-field-fiber`), `X`, `Y` schemes of finite type over `k` (separatedness is not
needed), and `Λ` a finite ring whose exponent is invertible in `k`. This covers the rings
`A = 𝒪_E/ϖ_E^n` of the blueprint, `E/ℚ_ℓ` finite and `ℓ ≠ char k`
(`AlgebraicGeometry.Etale.nonempty_iso_kunneth_quotient_pow`). For all `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, with `K ⊠ᴸ L = Lp_X^* K ⊗ᴸ Lp_Y^* L` on `X ×_k Y`,

`RΓ(X, K) ⊗ᴸ RΓ(Y, L) ≅ RΓ(X ×_k Y, K ⊠ᴸ L)`

in `D(Λ)`. This isomorphism is `RΓ(Spec k, -)` applied to the Künneth map
(`AlgebraicGeometry.Etale.kunnethMap`), which is an isomorphism by
`AlgebraicGeometry.Etale.isIso_kunnethMap_of_isSepClosed`; the statement is
`AlgebraicGeometry.Etale.nonempty_iso_kunneth_of_isSepClosed` for the fibre product square. -/
theorem nonempty_iso_kunneth_pullback_of_isSepClosed
    [HasInvertibleExponent Λ (Spec (.of k))]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj L ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (pullback aX aY)).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback aX aY)).obj
            ((L((pullback.fst aX aY)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          ((L((pullback.snd aX aY)^*[ModuleCat.{u + 1} Λ])).obj L))) :=
  nonempty_iso_kunneth_of_isSepClosed Λ aX aY _ _ (IsPullback.of_hasPullback aX aY) K L

/-- Blueprint `lem-pur-ordinary-kunneth-finite-ring`, for the coefficient rings
`A = 𝒪 ⧸ (ϖ ^ n)`: if `A` is finite and killed by a power of a natural number `ℓ` which is
invertible in the separably closed field `k` (for `𝒪 = 𝒪_E`, `E/ℚ_ℓ` finite, and
`ℓ ≠ char k`), then `RΓ(X, K) ⊗ᴸ RΓ(Y, L) ≅ RΓ(X ×_k Y, K ⊠ᴸ L)` for `X`, `Y` of finite type
over `k`. -/
theorem nonempty_iso_kunneth_quotient_pow {𝒪 : Type (u + 1)} [CommRing 𝒪] (ϖ : 𝒪) (n : ℕ)
    [Finite (𝒪 ⧸ Ideal.span {ϖ ^ n})] {ℓ m : ℕ} (hℓ : (ℓ : k) ≠ 0)
    (hA : ((ℓ ^ m : ℕ) : 𝒪 ⧸ Ideal.span {ϖ ^ n}) = 0)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n}))))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})))) :
    Nonempty
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})) X).obj K ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})) Y).obj L ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n}))
          (pullback aX aY)).obj
        (((derivedTensor (ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})) (pullback aX aY)).obj
            ((L((pullback.fst aX aY)^*[ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})])).obj
              K)).obj
          ((L((pullback.snd aX aY)^*[ModuleCat.{u + 1} (𝒪 ⧸ Ideal.span {ϖ ^ n})])).obj L))) :=
  have := HasInvertibleExponent.spec_of_pow_eq_zero (𝒪 ⧸ Ideal.span {ϖ ^ n}) hℓ hA
  nonempty_iso_kunneth_pullback_of_isSepClosed _ aX aY K L

end Etale

end AlgebraicGeometry
