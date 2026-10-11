/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!

# The Künneth–Verdier comparison maps on the étale site

## Main definitions

- `AlgebraicGeometry.Etale.HasKunnethComparisons` (`sk-def-sf-kv-maps`, `def-sf-kv-maps`): the
  four product comparison assertions `Ku_!`, `α`, `β`, `κ`, one per field.

## Main statements

- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`sk-thm-sf-kunneth-verdier`): the four
  comparison maps are isomorphisms.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {B X Y : Scheme.{u}}

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-def-sf-kv-maps`, `def-sf-kv-maps`: The product comparison maps.

The four product comparison maps of the six-functor formalism over a base scheme `S`, each
recorded as the assertion that it is an isomorphism. All external products are taken over
`S`.

* `kunnethShriek` is the `!`-Künneth map
  `Ku_! : Rf_! (M₁ ⊠ M₂) ⟶ Rf_{1!} M₁ ⊠ Rf_{2!} M₂` for `f = f₁ × f₂`, which is
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct` for the base
  `Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_S Y₂) ×_{Y₁ ×_S Y₂} (Y₁ ×_S X₂)`; it is an
  isomorphism *by construction*, being built out of isomorphisms. For a finite coefficient
  ring this is proved, from the relative product theorem and compact-support base change, as
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`;
* `exceptional` is the exceptional Künneth map
  `α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ⟶ Rf^! (N₁ ⊠ N₂)`, the exceptional adjoint of `Ku_!` followed by
  the two counits of `Rf_{i!} ⊣ Rf_i^!`;
* `externalHom` is the external Hom map
  `β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ⟶ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`, the tensor–Hom transpose of
  the two evaluation maps;
* `kunnethVerdier` is the Künneth–Verdier map
  `κ : M ⊠ 𝔻_Y N ⟶ RHom(p_Y^* N, Rp_X^! M)` on `X ×_S Y`, the composite of `β` applied to the
  pairs `(Λ_X, M)` and `(N, ω_Y)` with `RHom(1, α)` for `id_X × a_Y`, using the unit
  identifications `RHom(Λ_X, M) = M` and `Λ_X ⊠ N = p_Y^* N`.

Only `Ku_!` is built from isomorphisms; that `α`, `β` and `κ` are invertible is the content of
`AlgebraicGeometry.Etale.hasKunnethComparisons`, i.e. of `sk-thm-sf-kunneth-verdier`, which
holds over a field for finite coefficients of invertible exponent. Over a more general base the
comparisons fail: over `S = 𝔸¹_k`, with `E₁ = E₂ = i_*Λ` the skyscraper at the origin and
`N₁ = N₂ = Λ_S`, the source of `β` is `i_*Λ(-2)[-4]` and its target `i_*Λ(-1)[-2]`. -/
structure HasKunnethComparisons (S : Scheme.{u}) : Prop where
  /-- The `!`-Künneth map `Ku_!` is an isomorphism. -/
  kunnethShriek : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      {M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A)}
      {M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A X₁ M₁ →
      DerivedCategory.constructibleFiniteTor A X₂ M₂ →
      Nonempty ((R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).obj
          (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) ≅
        externalProduct A b₁ b₂ ((R(f₁)_![A]).obj M₁) ((R(f₂)_![A]).obj M₂))
  /-- The exceptional Künneth map `α` is an isomorphism. -/
  exceptional : ∀ {X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S)
      [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
      (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
      [QuasiCompact f₁] [QuasiCompact f₂]
      [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
      [(R(f₁)_![A]).IsLeftAdjoint] [(R(f₂)_![A]).IsLeftAdjoint]
      [(R(pullback.mapOverBase f₁ f₂ b₁ b₂)_![A]).IsLeftAdjoint]
      {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology A)}
      {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A Y₁ N₁ →
      DerivedCategory.constructibleFiniteTor A Y₂ N₂ →
      Nonempty (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂)
          ((R(f₁)^![A]).obj N₁) ((R(f₂)^![A]).obj N₂) ≅
        (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![A]).obj (externalProduct A b₁ b₂ N₁ N₂))
  /-- The external Hom map `β` is an isomorphism. -/
  externalHom : ∀ {Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
      [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
      [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
      {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A)}
      {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A Z₁ E₁ →
      DerivedCategory.constructibleFiniteTor A Z₂ E₂ →
      DerivedCategory.constructibleFiniteTor A Z₁ N₁ →
      DerivedCategory.constructibleFiniteTor A Z₂ N₂ →
      Nonempty (externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj N₁)
          ((RHom(Z₂)[A].obj (op E₂)).obj N₂) ≅
        (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
          (externalProduct A c₁ c₂ N₁ N₂))
  /-- The Künneth–Verdier map `κ` is an isomorphism. -/
  kunnethVerdier : ∀ {X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
      [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
      [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
      [(R(b)_![A]).IsLeftAdjoint] [(R(pullback.fst a b)_![A]).IsLeftAdjoint]
      {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
      {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)},
      DerivedCategory.constructibleFiniteTor A X M →
      DerivedCategory.constructibleFiniteTor A Y N →
      Nonempty (externalProduct A a b M ((verdierDual A b).obj (op N)) ≅
        (RHom(pullback a b)[A].obj (op ((L((pullback.snd a b)^*[A])).obj N))).obj
          ((R(pullback.fst a b)^![A]).obj M))

omit [HasSmallSiteSheafify A] in
/-- The external Hom map `β` of `AlgebraicGeometry.Etale.HasKunnethComparisons` is an isomorphism
for **dualizable** `E₁`, `E₂`:
`RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`. The derived pullbacks are monoidal and
preserve duals, and internal homs out of dualizable objects are tensor products with the duals
(`CategoryTheory.nonempty_iso_tensorObj_map_ihom_obj`). Over a field, constructible complexes of
finite Tor amplitude are dualizable only where they are lisse, so this is the lisse case of the
`externalHom` clause. -/
theorem nonempty_iso_externalProduct_derivedHom_of_isDualizable [UpperStarPreservesFlat A]
    {S Z₁ Z₂ : Scheme.{u}} (c₁ : Z₁ ⟶ S) (c₂ : Z₂ ⟶ S)
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology A)}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology A)}
    (h₁ : IsDualizable E₁) (h₂ : IsDualizable E₂) :
    Nonempty (externalProduct A c₁ c₂ ((RHom(Z₁)[A].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[A].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[A].obj (op (externalProduct A c₁ c₂ E₁ E₂))).obj
        (externalProduct A c₁ c₂ N₁ N₂)) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Z₁.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Z₂.smallEtaleTopology A)
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (pullback c₁ c₂).smallEtaleTopology A)
  let _ := leftDerivedUpperStarMonoidal A (pullback.fst c₁ c₂)
  let _ := leftDerivedUpperStarMonoidal A (pullback.snd c₁ c₂)
  exact nonempty_iso_tensorObj_map_ihom_obj (L((pullback.fst c₁ c₂)^*[A]))
    (L((pullback.snd c₁ c₂)^*[A])) h₁ h₂

/-- Blueprint `sk-thm-sf-kunneth-verdier`: Künneth–Verdier isomorphism.

The four product comparison maps of `AlgebraicGeometry.Etale.HasKunnethComparisons` are
isomorphisms: besides the `!`-Künneth map `Ku_!`, which is an isomorphism by construction,
this asserts the invertibility of the exceptional Künneth map `α`, of the external Hom map
`β`, and of the Künneth–Verdier map `κ`.

It is stated over a field `k`, for a finite coefficient ring `Λ` whose exponent is invertible
in `k`, as in the blueprint. The headline case is `kunnethVerdier`: for `X` and `Y` separated of
finite type over `S = Spec k`,
with projections `p_X : X ×_S Y ⟶ X` and `p_Y : X ×_S Y ⟶ Y`, and for `M` in `Dctf(X, A)`
and `N` in `Dctf(Y, A)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`

on `X ×_S Y`, where `𝔻_Y = RHom(-, ω_Y)` is the Verdier dual relative to `b : Y ⟶ S`. -/
theorem hasKunnethComparisons (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (k : Type u)
    [Field k] [HasInvertibleExponent Λ (Spec (.of k))] :
    HasKunnethComparisons (ModuleCat.{u + 1} Λ) (Spec (.of k)) where
  kunnethShriek := by
    intro _ _ _ _ b₁ b₂ _ _ _ _ f₁ f₂ _ _ _ _ _ _ _ hM₁ hM₂
    exact nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct (Λ := Λ) b₁ b₂ f₁ f₂
      hM₁ hM₂
  exceptional := sorry
  externalHom := sorry
  kunnethVerdier := sorry

end Etale

end AlgebraicGeometry
