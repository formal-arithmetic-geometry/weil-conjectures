/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Formal
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalComp

/-!

# The external Hom isomorphism from the Künneth–Verdier isomorphism

Over an algebraically closed field `k`, Verdier biduality turns the Künneth–Verdier isomorphism
`κ` into the statement that Verdier duality commutes with external products,
`𝔻(A ⊠ B) ≅ 𝔻A ⊠ 𝔻B` (`AlgebraicGeometry.Etale.kunnethVerdier_iff_verdierDual_externalProduct`),
and this gives the external Hom isomorphism `β` of `prop-trf-external-hom`:

`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ 𝔻(𝔻N₁ ⊗ E₁) ⊠ 𝔻(𝔻N₂ ⊗ E₂) ≅ 𝔻((𝔻N₁ ⊗ E₁) ⊠ (𝔻N₂ ⊗ E₂))
  ≅ 𝔻((𝔻N₁ ⊠ 𝔻N₂) ⊗ (E₁ ⊠ E₂)) ≅ 𝔻(𝔻(N₁ ⊠ N₂) ⊗ (E₁ ⊠ E₂)) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`,

using `RHom(E, N) ≅ RHom(E, 𝔻𝔻N) ≅ 𝔻(𝔻N ⊗ E)` (biduality and the internal adjunction).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom_of_kunnethVerdier`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- `RHom(E, N) ≅ 𝔻(𝔻N ⊗ E)` for `N ∈ Dctf`, by biduality and the internal adjunction. -/
lemma nonempty_iso_derivedHom_verdierDual_derivedTensor {Z : Scheme.{u}} (c : Z ⟶ Spec (.of k))
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (E : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    {N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z N) :
    Nonempty ((RHom(Z)[ModuleCat.{u + 1} Λ].obj (op E)).obj N ≅
      (verdierDual (ModuleCat.{u + 1} Λ) c).obj (op (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
        ((verdierDual (ModuleCat.{u + 1} Λ) c).obj (op N))).obj E))) := by
  obtain ⟨bi⟩ := nonempty_iso_verdierDual_verdierDual Λ c hN
  exact ⟨((RHom(Z)[ModuleCat.{u + 1} Λ]).obj (op E)).mapIso bi ≪≫
    (MonoidalClosed.ihomTensorObjIso _ _ _).symm⟩

/-- Blueprint `prop-trf-external-hom`: External Hom; the `β` map, from the Künneth–Verdier
isomorphism `κ` (`thm-trf-kunneth-verdier`) for `Z₁`, `Z₂`.

For `Z₁`, `Z₂` separated of finite type over an algebraically closed field `k`, if `κ` holds for
`(Z₁, Z₂)`, then for `Eᵢ, Nᵢ ∈ Dctf(Zᵢ, Λ)`,
`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`: by biduality `κ` says that Verdier
duality commutes with external products
(`AlgebraicGeometry.Etale.kunnethVerdier_iff_verdierDual_externalProduct`), and
`RHom(E, N) ≅ 𝔻(𝔻N ⊗ E)`. -/
theorem nonempty_iso_externalProduct_derivedHom_of_kunnethVerdier {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    (hκ : ∀ {M : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
        {N : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))},
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ M →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N →
        Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ M
            ((verdierDual (ModuleCat.{u + 1} Λ) c₂).obj (op N)) ≅
          (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj
              (op ((L((pullback.snd c₁ c₂)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
            ((R(pullback.fst c₁ c₂)^![ModuleCat.{u + 1} Λ]).obj M)))
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
        ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj
          (op (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ E₂))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂)) := by
  obtain ⟨βP⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)
  have hDN₁ := constructibleFiniteTor_verdierDual Λ c₁ hN₁
  have hDN₂ := constructibleFiniteTor_verdierDual Λ c₂ hN₂
  have hA₁ := constructibleFiniteTor_tensor Λ Z₁ hDN₁ hE₁
  have hA₂ := constructibleFiniteTor_tensor Λ Z₂ hDN₂ hE₂
  have hNN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)
      (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂) :=
    constructibleFiniteTor_tensor Λ _ (constructibleFiniteTor_leftDerivedUpperStar _ _ hN₁)
      (constructibleFiniteTor_leftDerivedUpperStar _ _ hN₂)
  obtain ⟨h₁⟩ := nonempty_iso_derivedHom_verdierDual_derivedTensor Λ c₁ E₁ hN₁
  obtain ⟨h₂⟩ := nonempty_iso_derivedHom_verdierDual_derivedTensor Λ c₂ E₂ hN₂
  obtain ⟨δA⟩ := (kunnethVerdier_iff_verdierDual_externalProduct Λ c₁ c₂).1
    (fun hM hN ↦ hκ hM hN) hA₁ hA₂
  obtain ⟨δN⟩ := (kunnethVerdier_iff_verdierDual_externalProduct Λ c₁ c₂).1
    (fun hM hN ↦ hκ hM hN) hN₁ hN₂
  obtain ⟨bi⟩ := nonempty_iso_verdierDual_verdierDual Λ (pullback.fst c₁ c₂ ≫ c₁) hNN
  -- `(a ⊗ b) ⊗ (c ⊗ d) ≅ (a ⊗ c) ⊗ (b ⊗ d)`, written with `derivedTensor`
  let shuffle (a b c d : _root_.DerivedCategory
      (Sheaf (pullback c₁ c₂).smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      ((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj a).obj b)).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj c).obj d) ≅
        ((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj
          (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj a).obj c)).obj
            (((derivedTensor (ModuleCat.{u + 1} Λ) (pullback c₁ c₂)).obj b).obj d) :=
    derivedTensorAssociator _ _ a b _ ≪≫ derivedTensorMapIso Λ (Iso.refl a)
      ((derivedTensorAssociator _ _ b c d).symm ≪≫
        derivedTensorMapIso Λ ((βP.app b).app c) (Iso.refl d) ≪≫
        derivedTensorAssociator _ _ c b d) ≪≫ (derivedTensorAssociator _ _ a c _).symm
  let s : externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
      (((derivedTensor _ Z₁).obj ((verdierDual (ModuleCat.{u + 1} Λ) c₁).obj (op N₁))).obj E₁)
      (((derivedTensor _ Z₂).obj ((verdierDual (ModuleCat.{u + 1} Λ) c₂).obj (op N₂))).obj E₂) ≅
      ((derivedTensor _ _).obj (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
        ((verdierDual (ModuleCat.{u + 1} Λ) c₁).obj (op N₁))
        ((verdierDual (ModuleCat.{u + 1} Λ) c₂).obj (op N₂)))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ E₂) :=
    derivedTensorMapIso Λ (leftDerivedUpperStarTensorIso _ (pullback.fst c₁ c₂) _ _)
      (leftDerivedUpperStarTensorIso _ (pullback.snd c₁ c₂) _ _) ≪≫ shuffle _ _ _ _
  exact ⟨derivedTensorMapIso Λ ((L((pullback.fst c₁ c₂)^*[ModuleCat.{u + 1} Λ])).mapIso h₁)
      ((L((pullback.snd c₁ c₂)^*[ModuleCat.{u + 1} Λ])).mapIso h₂) ≪≫ δA.symm ≪≫
    ((verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst c₁ c₂ ≫ c₁)).mapIso s.op).symm ≪≫
    (verdierDual (ModuleCat.{u + 1} Λ) (pullback.fst c₁ c₂ ≫ c₁)).mapIso
      (derivedTensorMapIso Λ δN (Iso.refl _)).op ≪≫
    MonoidalClosed.ihomTensorObjIso _ _ _ ≪≫
    ((RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ]).obj _).mapIso bi.symm⟩

end Etale

end AlgebraicGeometry
