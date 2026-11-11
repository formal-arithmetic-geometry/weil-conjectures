/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative

/-!

# The ordinary external Künneth formula on the étale site

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and let
`f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` be morphisms of `k`-schemes of finite type. For
`M₁ ∈ D(X₁,ét, Λ)` and `M₂ ∈ D(X₂,ét, Λ)` the Künneth map

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_externalProductKunnethMap_of_finite`, blueprint
`proposition-ordinary-external-kunneth`).

Following the blueprint, `f₁ × f₂` is factored as
`X₁ ×_k X₂ ⟶ X₁ ×_k Y₂ ⟶ Y₁ ×_k Y₂` (`𝟙 × f₂` followed by `f₁ × 𝟙`), and the Künneth map is the
composite of the Künneth maps with one identity factor for `f₁`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`) and for `f₂`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`), and of the composition
isomorphism of direct images. Both factors are base change maps of `lem-kun-0f1n`
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`).

## Main definitions

- `AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`: the Künneth map
  `Q ⊠ Rf_* M ⟶ R(𝟙_Z × f)_* (Q ⊠ M)` with an identity first factor.
- `AlgebraicGeometry.Etale.externalProductKunnethMap`: the Künneth map
  `Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {S X Y Z : Scheme.{u}}

/-- The square
```
  Z ×_S X --𝟙 × f--> Z ×_S Y
     |                  |
    pr                 pr
     v                  v
     X -------f-------> Y
```
is cartesian. -/
lemma isPullback_map_id_snd (c : Z ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) :
    IsPullback (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))
      (pullback.snd c (f ≫ b)) (pullback.snd c b) f :=
  .of_right (h₁₂ := pullback.fst c b) (h₂₂ := b) (v₁₃ := c)
    (by simpa using IsPullback.of_hasPullback c (f ≫ b)) (by simp)
    (IsPullback.of_hasPullback c b)

/-- The comparison map `Q ⊠ Rf_* M ⟶ R(𝟙_Z × f)_* (Q ⊠ M)` of the ordinary Künneth formula with
an identity first factor, for `c : Z ⟶ S`, `b : Y ⟶ S`, `f : X ⟶ Y`, `Q ∈ D(Z_ét)` and
`M ∈ D(X_ét)`: the base change map `AlgebraicGeometry.Etale.tensorBaseChangeMap` of
`lem-kun-0f1n` for the cartesian square `AlgebraicGeometry.Etale.isPullback_map_id_snd`, followed
by the composition isomorphism `(𝟙 × f)^* p_Z^* ≅ p_Z^*`. It is the mirror image of
`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`. -/
noncomputable def externalProductRightDerivedLowerStarSndMap [UpperStarPreservesFlat A]
    (c : Z ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y)
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    externalProduct A c b Q ((R((f)_*[A])).obj M) ⟶
      (R((pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))_*[A])).obj
        (externalProduct A c (f ≫ b) Q M) :=
  tensorBaseChangeMap A (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))
      (pullback.snd c (f ≫ b)) (pullback.snd c b) f (isPullback_map_id_snd c b f).w
      ((L((pullback.fst c b)^*[A])).obj Q) M ≫
    (R((pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))_*[A])).map
      (((derivedTensor A (pullback c (f ≫ b))).map
        ((leftDerivedUpperStarComp A
          (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))
          (pullback.fst c b) (pullback.fst c (f ≫ b)) (by simp)).inv.app Q)).app _)

/-- The Künneth map `Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)` (blueprint
`definition-kunneth-map`) for `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` and `Yᵢ` over `S` through `bᵢ`,
built as in the proof of `proposition-ordinary-external-kunneth` along the factorization
`f₁ × f₂ = (𝟙 × f₂) ≫ (f₁ × 𝟙) : X₁ ×_S X₂ ⟶ X₁ ×_S Y₂ ⟶ Y₁ ×_S Y₂`: the Künneth map with an
identity factor for `f₁` at `(M₁, Rf₂_* M₂)`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`), then `R(f₁ × 𝟙)_*` of the
Künneth map with an identity factor for `f₂` at `(M₁, M₂)`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`), then the composition
isomorphism `R(f₁ × 𝟙)_* R(𝟙 × f₂)_* ≅ R(f₁ × f₂)_*`. -/
noncomputable def externalProductKunnethMap [UpperStarPreservesFlat A] {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    externalProduct A b₁ b₂ ((R((f₁)_*[A])).obj M₁) ((R((f₂)_*[A])).obj M₂) ⟶
      (R((pullback.mapOverBase f₁ f₂ b₁ b₂)_*[A])).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) :=
  externalProductRightDerivedLowerStarMap A b₁ b₂ f₁ M₁ ((R((f₂)_*[A])).obj M₂) ≫
    (R((pullback.mapOverBaseRight f₁ b₁ b₂)_*[A])).map
      (externalProductRightDerivedLowerStarSndMap A (f₁ ≫ b₁) b₂ f₂ M₁ M₂) ≫
    (rightDerivedLowerStarCompIsoOfComp A
      (pullback.map (f₁ ≫ b₁) (f₂ ≫ b₂) (f₁ ≫ b₁) b₂ (𝟙 X₁) f₂ (𝟙 S) (by simp) (by simp))
      (pullback.mapOverBaseRight f₁ b₁ b₂) (pullback.mapOverBase f₁ f₂ b₁ b₂)
      (by ext <;> simp)).hom.app _

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- The ordinary Künneth formula with an identity first factor, the mirror image of
`AlgebraicGeometry.Etale.isIso_externalProductRightDerivedLowerStarMap_of_finite`: over a field
`k`, for a finite ring `Λ` whose exponent is invertible in `k` and morphisms `c : Z ⟶ Spec k`,
`b : Y ⟶ Spec k` and `f : X ⟶ Y` of finite type, the comparison
`Q ⊠ Rf_* M ⟶ R(𝟙_Z × f)_* (Q ⊠ M)` is an isomorphism for all `Q ∈ D(Z_ét, Λ)` and
`M ∈ D(X_ét, Λ)`, by `lem-kun-0f1n` (`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`). -/
theorem isIso_externalProductRightDerivedLowerStarSndMap_of_finite (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]
    (c : Z ⟶ Spec (.of k)) (b : Y ⟶ Spec (.of k)) (f : X ⟶ Y)
    [LocallyOfFiniteType c] [QuasiCompact c] [LocallyOfFiniteType b] [QuasiCompact b]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (externalProductRightDerivedLowerStarSndMap (ModuleCat.{u + 1} Λ) c b f Q M) := by
  have := isIso_tensorBaseChangeMap Λ c b (f ≫ b) (pullback.fst c b) (pullback.snd c b)
    (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 _) (by simp) (by simp)) (pullback.snd c (f ≫ b)) f
    rfl (IsPullback.of_hasPullback c b) (isPullback_map_id_snd c b f) Q M
  rw [externalProductRightDerivedLowerStarSndMap]
  infer_instance

/-- **Ordinary external Künneth** (blueprint `proposition-ordinary-external-kunneth`, clause
`proposition-ordinary-external-kunneth--1`). Let `k` be a field, `Λ` a finite ring whose exponent
is invertible in `k`, and `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` morphisms of `k`-schemes of finite type
(with structure morphisms `bᵢ : Yᵢ ⟶ Spec k`, and `Xᵢ` over `k` through `fᵢ ≫ bᵢ`). Then for
`M₁ ∈ D(X₁,ét, Λ)` and `M₂ ∈ D(X₂,ét, Λ)` the Künneth map
(`AlgebraicGeometry.Etale.externalProductKunnethMap`)

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`

is an isomorphism. The blueprint assumes moreover that the schemes are separated and that
`Mᵢ ∈ Dᵇctf(Xᵢ, Λ)`; neither hypothesis is needed. As in the blueprint proof, the Künneth map is
the composite of the Künneth maps with one identity factor for `f₁`
(`isIso_externalProductRightDerivedLowerStarMap_of_finite`, blueprint
`lemma-kunneth-one-identity-factor`) and for `f₂`
(`isIso_externalProductRightDerivedLowerStarSndMap_of_finite`) and of a composition
isomorphism. -/
theorem isIso_externalProductKunnethMap_of_finite (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k)) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    [LocallyOfFiniteType f₁] [QuasiCompact f₁] [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (externalProductKunnethMap (ModuleCat.{u + 1} Λ) b₁ b₂ f₁ f₂ M₁ M₂) := by
  have := isIso_tensorBaseChangeMap Λ b₂ b₁ (f₁ ≫ b₁) (pullback.snd b₁ b₂) (pullback.fst b₁ b₂)
    (pullback.mapOverBaseRight f₁ b₁ b₂) (pullback.fst (f₁ ≫ b₁) b₂) f₁ rfl
    (IsPullback.of_hasPullback b₁ b₂).flip (isPullback_mapOverBaseRight_fst b₁ b₂ f₁)
    ((R((f₂)_*[ModuleCat.{u + 1} Λ])).obj M₂) M₁
  have := isIso_externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b₁ b₂ f₁ M₁
    ((R((f₂)_*[ModuleCat.{u + 1} Λ])).obj M₂)
  have := isIso_externalProductRightDerivedLowerStarSndMap_of_finite Λ (f₁ ≫ b₁) b₂ f₂ M₁ M₂
  rw [externalProductKunnethMap]
  infer_instance

end Etale

end AlgebraicGeometry
