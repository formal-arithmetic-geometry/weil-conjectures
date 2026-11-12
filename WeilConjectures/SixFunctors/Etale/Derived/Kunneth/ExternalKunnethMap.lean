/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The external Künneth map

Let `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` be morphisms of schemes with `Y₁`, `Y₂` over a base `S`,
and put `h = f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂` (`CategoryTheory.Limits.pullback.mapOverBase`).
For `M₁ ∈ D(X₁,ét)` and `M₂ ∈ D(X₂,ét)` the *Künneth map*

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ Rh_* (M₁ ⊠ M₂)`

is the adjoint transpose, for `Lh^* ⊣ Rh_*`, of the morphism

`Lh^* (Rf₁_* M₁ ⊠ Rf₂_* M₂) ⟶ Lf₁^* Rf₁_* M₁ ⊠ Lf₂^* Rf₂_* M₂ ⟶ M₁ ⊠ M₂`

built from the monoidality of `Lh^*`, the composition isomorphisms `Lh^* Lpᵢ^* ≅ Lqᵢ^* Lfᵢ^*`
for the projections `pᵢ` of `Y₁ ×_S Y₂` and `qᵢ` of `X₁ ×_S X₂`, and the counits of
`Lfᵢ^* ⊣ Rfᵢ_*`.

## Main definitions

- `AlgebraicGeometry.Etale.externalKunnethMap` (`definition-kunneth-map`): the Künneth map.

## Main statements

- `AlgebraicGeometry.Etale.map_externalKunnethMap_comp_counit`: the Künneth map is the adjoint
  transpose of `ε_{f₁} ⊠ ε_{f₂}`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

variable {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁)
  (f₂ : X₂ ⟶ Y₂)

/-- The morphism `Lh^* (Rf₁_* M₁ ⊠ Rf₂_* M₂) ⟶ M₁ ⊠ M₂` for `h = f₁ × f₂`: the monoidality of
`Lh^*`, followed on the `i`-th factor by the composition isomorphisms
`Lh^* Lpᵢ^* ≅ L(qᵢ ≫ fᵢ)^* ≅ Lqᵢ^* Lfᵢ^*` and `Lqᵢ^*` of the counit of `Lfᵢ^* ⊣ Rfᵢ_*`. Its
adjoint transpose is the Künneth map `AlgebraicGeometry.Etale.externalKunnethMap`. -/
noncomputable def externalKunnethMapAdj
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    (L((pullback.mapOverBase f₁ f₂ b₁ b₂)^*[A])).obj
        (externalProduct A b₁ b₂ ((R((f₁)_*[A])).obj M₁) ((R((f₂)_*[A])).obj M₂)) ⟶
      externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂ :=
  ((leftDerivedUpperStarTensorComparison A (pullback.mapOverBase f₁ f₂ b₁ b₂)).app _).app _ ≫
    ((derivedTensor A (pullback (f₁ ≫ b₁) (f₂ ≫ b₂))).map
      ((leftDerivedUpperStarComp A (pullback.mapOverBase f₁ f₂ b₁ b₂) (pullback.fst b₁ b₂)
          (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₁) (by simp)).inv.app _ ≫
        (leftDerivedUpperStarComp A (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂)) f₁).hom.app _ ≫
        (L((pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).map
          ((derivedUpperStarLowerStarAdjunction A f₁).counit.app M₁))).app _ ≫
    ((derivedTensor A (pullback (f₁ ≫ b₁) (f₂ ≫ b₂))).obj _).map
      ((leftDerivedUpperStarComp A (pullback.mapOverBase f₁ f₂ b₁ b₂) (pullback.snd b₁ b₂)
          (pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂) ≫ f₂) (by simp)).inv.app _ ≫
        (leftDerivedUpperStarComp A (pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂)) f₂).hom.app _ ≫
        (L((pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂))^*[A])).map
          ((derivedUpperStarLowerStarAdjunction A f₂).counit.app M₂))

/-- Blueprint `definition-kunneth-map`: the Künneth map.

For `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` with `Y₁`, `Y₂` over `S` through `b₁`, `b₂`, put
`h = f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂`. For `M₁ ∈ D(X₁,ét)` and `M₂ ∈ D(X₂,ét)` the Künneth map

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ Rh_* (M₁ ⊠ M₂)`

is the adjoint transpose, for `Lh^* ⊣ Rh_*`, of the morphism
`Lh^* (Rf₁_* M₁ ⊠ Rf₂_* M₂) ⟶ Lf₁^* Rf₁_* M₁ ⊠ Lf₂^* Rf₂_* M₂ ⟶ M₁ ⊠ M₂`
(`AlgebraicGeometry.Etale.externalKunnethMapAdj`) given by the monoidality of `Lh^*`, the
isomorphisms `Lh^* Lpᵢ^* ≅ Lqᵢ^* Lfᵢ^*` and the counits `ε_{fᵢ}` of `Lfᵢ^* ⊣ Rfᵢ_*`.

The blueprint takes `S = Spec k`, separated `k`-schemes of finite type and
`Mᵢ ∈ Dᵇ_ctf(Xᵢ, A)`; none of these hypotheses is needed to define the map. -/
noncomputable def externalKunnethMap
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    externalProduct A b₁ b₂ ((R((f₁)_*[A])).obj M₁) ((R((f₂)_*[A])).obj M₂) ⟶
      (R((pullback.mapOverBase f₁ f₂ b₁ b₂)_*[A])).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) :=
  (derivedUpperStarLowerStarAdjunction A (pullback.mapOverBase f₁ f₂ b₁ b₂)).homEquiv _ _
    (externalKunnethMapAdj A b₁ b₂ f₁ f₂ M₁ M₂)

/-- Blueprint `definition-kunneth-map`: the Künneth map
`AlgebraicGeometry.Etale.externalKunnethMap` is the adjoint transpose of
`AlgebraicGeometry.Etale.externalKunnethMapAdj`: applying `Lh^*` and composing with the counit
of `Lh^* ⊣ Rh_*` recovers `ε_{f₁} ⊠ ε_{f₂}` precomposed with the monoidality of `Lh^*`. -/
@[reassoc]
lemma map_externalKunnethMap_comp_counit
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    (L((pullback.mapOverBase f₁ f₂ b₁ b₂)^*[A])).map (externalKunnethMap A b₁ b₂ f₁ f₂ M₁ M₂) ≫
        (derivedUpperStarLowerStarAdjunction A (pullback.mapOverBase f₁ f₂ b₁ b₂)).counit.app _ =
      externalKunnethMapAdj A b₁ b₂ f₁ f₂ M₁ M₂ :=
  ((derivedUpperStarLowerStarAdjunction A _).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

end Etale

end AlgebraicGeometry
