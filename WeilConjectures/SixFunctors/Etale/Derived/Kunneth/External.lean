/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperFactor.KunnethMapAgrees
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative

/-!

# The ordinary external Künneth formula on the étale site

Let `k` be a field, `Λ` a finite ring whose exponent is invertible in `k`, and let
`f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` be morphisms of `k`-schemes of finite type. For
`M₁ ∈ D(X₁,ét, Λ)` and `M₂ ∈ D(X₂,ét, Λ)` the Künneth map

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_externalProductKunnethMap_of_finite`).

## Main definitions

- `AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`: the Künneth map
  `Q ⊠ Rf_* M ⟶ R(𝟙_Z × f)_* (Q ⊠ M)` with an identity first factor.
- `AlgebraicGeometry.Etale.kunnethMapOfSquares`: the Künneth map
  `Lπ₁^* Rf₁_* M₁ ⊗ᴸ Lπ₂^* Rf₂_* M₂ ⟶ Rh_* (Lq₁^* M₁ ⊗ᴸ Lq₂^* M₂)` of two commutative squares
  `h ≫ πᵢ = qᵢ ≫ fᵢ`, the transpose of `ε_{f₁} ⊠ ε_{f₂}`.
- `AlgebraicGeometry.Etale.externalProductKunnethMap`: the Künneth map
  `Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`.

## Main statements

- `AlgebraicGeometry.Etale.externalProductKunnethMap_eq`: the Künneth map is the composite of the
  Künneth maps with one identity factor.
- `AlgebraicGeometry.Etale.isIso_externalProductKunnethMap_of_finite`: the Künneth formula.

## Implementation details

`f₁ × f₂` is factored as `X₁ ×_k X₂ ⟶ X₁ ×_k Y₂ ⟶ Y₁ ×_k Y₂` (`𝟙 × f₂` followed by `f₁ × 𝟙`).
The transposes of the Künneth maps with one identity factor for `f₁`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`) and for `f₂`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`) are computed by
`AlgebraicGeometry.Etale.map_externalProductRightDerivedLowerStarMap_comp_counit` and
`AlgebraicGeometry.Etale.map_externalProductRightDerivedLowerStarSndMap_comp_counit`; pasting them
gives `ε_{f₁} ⊠ ε_{f₂}`, so the Künneth map is their composite with the composition isomorphism of
direct images. Both factors are tensor base change maps
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`), invertible by
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`. The theorem holds without the hypotheses
that the schemes are separated and that `Mᵢ` is bounded constructible of finite Tor-dimension.

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
`M ∈ D(X_ét)`: the tensor base change map for the cartesian square
`AlgebraicGeometry.Etale.isPullback_map_id_snd`, followed by the composition isomorphism
`(𝟙 × f)^* p_Z^* ≅ p_Z^*`. -/
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

attribute [local instance] _root_.DerivedCategory.braidedCategory'

/-- Precomposition with a component of the symmetry `AlgebraicGeometry.Etale.derivedTensorBraiding`,
retyped as `AlgebraicGeometry.Etale.derivedTensorBraidingIso`. -/
private lemma derivedTensorBraiding_hom_app_app_comp {W : Scheme.{u}}
    (P Q : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    {Z : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)}
    (g : ((-⊗ᴸ-(W)[A]).obj Q).obj P ⟶ Z) :
    ((derivedTensorBraiding A W).hom.app P).app Q ≫ g =
      (derivedTensorBraidingIso A W P Q).hom ≫ g :=
  rfl

/-- Postcomposition with a component of the symmetry
`AlgebraicGeometry.Etale.derivedTensorBraiding`, retyped as
`AlgebraicGeometry.Etale.derivedTensorBraidingIso`. -/
private lemma comp_derivedTensorBraiding_hom_app_app {W : Scheme.{u}}
    (P Q : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    {Z : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)}
    (g : Z ⟶ ((-⊗ᴸ-(W)[A]).obj P).obj Q) :
    (g ≫ ((derivedTensorBraiding A W).hom.app P).app Q : Z ⟶ ((-⊗ᴸ-(W)[A]).obj Q).obj P) =
      g ≫ (derivedTensorBraidingIso A W P Q).hom :=
  rfl

/-- The components of `AlgebraicGeometry.Etale.derivedTensorBraiding` are the braidings of
`D(X_ét)`. -/
private lemma derivedTensorBraiding_app_app_hom {W : Scheme.{u}}
    (K L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (derivedTensorBraidingIso A W K L).hom = (β_ K L).hom := by
  simp only [derivedTensorBraidingIso, derivedTensorBraiding, Iso.app_hom,
    BraidedCategory.curriedBraidingNatIso_hom_app_app]

/-- The tensor comparison of `Lg^*` commutes with the symmetry of `⊗ᴸ`. -/
@[reassoc]
private lemma leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison
    [UpperStarPreservesFlat A] {T W : Scheme.{u}} (g : T ⟶ W)
    (K L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (L((g)^*[A])).map (derivedTensorBraidingIso A W K L).hom ≫
        ((leftDerivedUpperStarTensorComparison A g).app L).app K =
      ((leftDerivedUpperStarTensorComparison A g).app K).app L ≫
        (derivedTensorBraidingIso A T ((L((g)^*[A])).obj K) ((L((g)^*[A])).obj L)).hom := by
  rw [derivedTensorBraiding_app_app_hom, derivedTensorBraiding_app_app_hom]
  exact leftDerivedUpperStar_map_braiding_hom_comp_tensorComparison A g K L

/-- The symmetry of `⊗ᴸ` is involutive. -/
@[reassoc]
private lemma derivedTensorBraiding_app_app_hom_comp {W : Scheme.{u}}
    (K L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    (derivedTensorBraidingIso A W K L).hom ≫
        (derivedTensorBraidingIso A W L K).hom = 𝟙 _ := by
  rw [derivedTensorBraiding_app_app_hom, derivedTensorBraiding_app_app_hom]
  exact (_root_.DerivedCategory.symmetricCategory _).symmetry K L

/-- Naturality of the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`. -/
@[reassoc]
private lemma map_leftDerivedUpperStarComp_hom_app {T T' W : Scheme.{u}} (g₁ : T ⟶ T')
    (g₂ : T' ⟶ W) (g₁₂ : T ⟶ W) (hg : g₁₂ = g₁ ≫ g₂)
    {K K' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)} (φ : K ⟶ K') :
    (L((g₁₂)^*[A])).map φ ≫ (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K' =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K ≫
        (L((g₁)^*[A])).map ((L((g₂)^*[A])).map φ) :=
  (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.naturality φ

/-- Naturality of the inverse of the composition isomorphism `L(g₁ ≫ g₂)^* ≅ Lg₂^* ⋙ Lg₁^*`. -/
@[reassoc]
private lemma map_map_leftDerivedUpperStarComp_inv_app {T T' W : Scheme.{u}} (g₁ : T ⟶ T')
    (g₂ : T' ⟶ W) (g₁₂ : T ⟶ W) (hg : g₁₂ = g₁ ≫ g₂)
    {K K' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)} (φ : K ⟶ K') :
    (L((g₁)^*[A])).map ((L((g₂)^*[A])).map φ) ≫
        (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app K' =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.app K ≫ (L((g₁₂)^*[A])).map φ :=
  (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).inv.naturality φ

/-- The two variables of `⊗ᴸ` are functorial independently of each other. -/
@[reassoc]
private lemma derivedTensor_map_app_comp_obj_map {W : Scheme.{u}}
    {K K' L L' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)} (φ : K ⟶ K')
    (ψ : L ⟶ L') :
    ((-⊗ᴸ-(W)[A]).map φ).app L ≫ ((-⊗ᴸ-(W)[A]).obj K').map ψ =
      ((-⊗ᴸ-(W)[A]).obj K).map ψ ≫ ((-⊗ᴸ-(W)[A]).map φ).app L' :=
  (((-⊗ᴸ-(W)[A]).map φ).naturality ψ).symm

/-- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp_derivedTensor`, with the two
composition isomorphisms applied in the other order. -/
@[reassoc]
private lemma leftDerivedUpperStarTensorComparison_comp_derivedTensor' [UpperStarPreservesFlat A]
    {T T' W : Scheme.{u}} (g₁ : T ⟶ T') (g₂ : T' ⟶ W) (g₁₂ : T ⟶ W) (hg : g₁₂ = g₁ ≫ g₂)
    (K L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app L ≫
        ((-⊗ᴸ-(T)[A]).obj _).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app L) ≫
        ((-⊗ᴸ-(T)[A]).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K)).app _ =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (((-⊗ᴸ-(W)[A]).obj K).obj L) ≫
        (L((g₁)^*[A])).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app L) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ := by
  rw [← derivedTensor_map_app_comp_obj_map]
  exact leftDerivedUpperStarTensorComparison_comp_derivedTensor A g₁ g₂ g₁₂ hg K L

/-- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp_derivedTensor'`, followed
by two morphisms in each variable. -/
private lemma leftDerivedUpperStarTensorComparison_comp_derivedTensor_comp
    [UpperStarPreservesFlat A] {T T' W : Scheme.{u}} (g₁ : T ⟶ T') (g₂ : T' ⟶ W) (g₁₂ : T ⟶ W)
    (hg : g₁₂ = g₁ ≫ g₂) (K L : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A))
    {K₁ K₂ L₁ L₂ : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)}
    (α₁ : (L((g₁)^*[A])).obj ((L((g₂)^*[A])).obj L) ⟶ L₁) (α₂ : L₁ ⟶ L₂)
    (β₁ : (L((g₁)^*[A])).obj ((L((g₂)^*[A])).obj K) ⟶ K₁) (β₂ : K₁ ⟶ K₂) :
    ((leftDerivedUpperStarTensorComparison A g₁₂).app K).app L ≫
        ((-⊗ᴸ-(T)[A]).obj _).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app L) ≫
        ((-⊗ᴸ-(T)[A]).obj _).map α₁ ≫ ((-⊗ᴸ-(T)[A]).obj _).map α₂ ≫
        ((-⊗ᴸ-(T)[A]).map ((leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app K)).app _ ≫
        ((-⊗ᴸ-(T)[A]).map β₁).app _ ≫ ((-⊗ᴸ-(T)[A]).map β₂).app _ =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ hg).hom.app (((-⊗ᴸ-(W)[A]).obj K).obj L) ≫
        (L((g₁)^*[A])).map (((leftDerivedUpperStarTensorComparison A g₂).app K).app L) ≫
        ((leftDerivedUpperStarTensorComparison A g₁).app _).app _ ≫
        ((-⊗ᴸ-(T)[A]).obj _).map α₁ ≫ ((-⊗ᴸ-(T)[A]).obj _).map α₂ ≫
        ((-⊗ᴸ-(T)[A]).map β₁).app _ ≫ ((-⊗ᴸ-(T)[A]).map β₂).app _ := by
  rw [← derivedTensor_map_app_comp_obj_map_assoc A _ α₂,
    ← derivedTensor_map_app_comp_obj_map_assoc A _ α₁,
    leftDerivedUpperStarTensorComparison_comp_derivedTensor'_assoc]
  rfl

/-- Naturality of the counit of `Lh^* ⊣ Rh_*`, written with `Lh^*` and `Rh_*`. -/
@[reassoc]
private lemma map_map_derivedUpperStarLowerStarAdjunction_counit {W X' : Scheme.{u}} (h : W ⟶ X')
    {K K' : _root_.DerivedCategory (Sheaf W.smallEtaleTopology A)} (φ : K ⟶ K') :
    (L((h)^*[A])).map ((R((h)_*[A])).map φ) ≫
        (derivedUpperStarLowerStarAdjunction A h).counit.app K' =
      (derivedUpperStarLowerStarAdjunction A h).counit.app K ≫ φ :=
  (derivedUpperStarLowerStarAdjunction A h).counit.naturality φ

/-- The transpose along `Lh^* ⊣ Rh_*` of the base change map
`AlgebraicGeometry.Etale.tensorBaseChangeMap` is the tensor comparison of `Lh^*` followed by the
counit morphism `AlgebraicGeometry.Etale.tensorBaseChangeCounitApp` on the second factor. -/
@[reassoc]
lemma map_tensorBaseChangeMap_comp_counit [UpperStarPreservesFlat A] {X' S' T W : Scheme.{u}}
    (h : W ⟶ X') (e : W ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (M : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    (L((h)^*[A])).map (tensorBaseChangeMap A h e f' g w M F) ≫
        (derivedUpperStarLowerStarAdjunction A h).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A h).app _).app _ ≫
        ((-⊗ᴸ-(W)[A]).obj _).map (tensorBaseChangeCounitApp A h e f' g w F) := by
  refine ((derivedUpperStarLowerStarAdjunction A h).homEquiv_counit _ _ _).symm.trans ?_
  rw [tensorBaseChangeMap]
  exact Equiv.symm_apply_apply _ _

set_option maxHeartbeats 800000 in
-- The rewrites match large terms of derived categories of étale sheaves.
/-- The composite of `L(f × 𝟙_Z)^*` of the comparison map
`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap` with the counit of
`L(f × 𝟙_Z)^* ⊣ R(f × 𝟙_Z)_*`: the tensor comparison of `L(f × 𝟙_Z)^*`, followed by the counit
morphism of `AlgebraicGeometry.Etale.tensorBaseChangeCounitApp` on the first factor and the
composition isomorphism `(f × 𝟙)^* p'_Z^* ≅ p_Z^*` on the second. -/
lemma map_externalProductRightDerivedLowerStarMap_comp_counit [UpperStarPreservesFlat A]
    (b : Y ⟶ S) (c : Z ⟶ S) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    (L((pullback.mapOverBaseRight f b c)^*[A])).map
        (externalProductRightDerivedLowerStarMap A b c f M Q) ≫
      (derivedUpperStarLowerStarAdjunction A (pullback.mapOverBaseRight f b c)).counit.app _ =
    ((leftDerivedUpperStarTensorComparison A (pullback.mapOverBaseRight f b c)).app _).app _ ≫
      ((-⊗ᴸ-(pullback (f ≫ b) c)[A]).map
        (tensorBaseChangeCounitApp A (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c)
          (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w M)).app _ ≫
      ((-⊗ᴸ-(pullback (f ≫ b) c)[A]).obj _).map
        ((leftDerivedUpperStarComp A (pullback.mapOverBaseRight f b c) (pullback.snd b c)
          (pullback.snd (f ≫ b) c) (by simp)).inv.app Q) := by
  rw [externalProductRightDerivedLowerStarMap]
  unfold externalProduct
  rw [derivedTensorBraiding_hom_app_app_comp,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  rw [map_map_derivedUpperStarLowerStarAdjunction_counit A (pullback.mapOverBaseRight f b c),
    map_tensorBaseChangeMap_comp_counit_assoc A (pullback.mapOverBaseRight f b c)
      (pullback.fst (f ≫ b) c) (pullback.fst b c) f _ ((L((pullback.snd b c)^*[A])).obj Q) M]
  rw [comp_derivedTensorBraiding_hom_app_app A ((L((pullback.snd (f ≫ b) c)^*[A])).obj Q)
    ((L((pullback.fst (f ≫ b) c)^*[A])).obj M)]
  rw [leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison_assoc A
    (pullback.mapOverBaseRight f b c) ((L((pullback.fst b c)^*[A])).obj ((R((f)_*[A])).obj M))
    ((L((pullback.snd b c)^*[A])).obj Q)]
  congr 1
  rw [← derivedTensorBraidingIso_hom_naturality_left_assoc,
    ← derivedTensorBraidingIso_hom_naturality_right_assoc,
    derivedTensorBraiding_app_app_hom_comp, Category.comp_id]

set_option maxHeartbeats 800000 in
-- The rewrites match large terms of derived categories of étale sheaves.
/-- The composite of `L(𝟙_Z × f)^*` of the comparison map
`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap` with the counit of
`L(𝟙_Z × f)^* ⊣ R(𝟙_Z × f)_*`. -/
lemma map_externalProductRightDerivedLowerStarSndMap_comp_counit [UpperStarPreservesFlat A]
    (c : Z ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y)
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))^*[A])).map
        (externalProductRightDerivedLowerStarSndMap A c b f Q M) ≫
      (derivedUpperStarLowerStarAdjunction A
        (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))).counit.app _ =
    ((leftDerivedUpperStarTensorComparison A
        (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))).app _).app _ ≫
      ((-⊗ᴸ-(pullback c (f ≫ b))[A]).obj _).map
        (tensorBaseChangeCounitApp A
          (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))
          (pullback.snd c (f ≫ b)) (pullback.snd c b) f (isPullback_map_id_snd c b f).w M) ≫
      ((-⊗ᴸ-(pullback c (f ≫ b))[A]).map
        ((leftDerivedUpperStarComp A
          (pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 S) (by simp) (by simp))
          (pullback.fst c b) (pullback.fst c (f ≫ b)) (by simp)).inv.app Q)).app _ := by
  rw [externalProductRightDerivedLowerStarSndMap]
  unfold externalProduct
  rw [Functor.map_comp, Category.assoc, map_map_derivedUpperStarLowerStarAdjunction_counit,
    map_tensorBaseChangeMap_comp_counit_assoc]

/-- The counit morphism `AlgebraicGeometry.Etale.tensorBaseChangeCounitApp` of a composite
`h = v ≫ u`, when the square of `u` is pasted with the composite `q = v ≫ r`. -/
private lemma tensorBaseChangeCounitApp_comp_of_fst [UpperStarPreservesFlat A]
    {W V P X' Y' : Scheme.{u}} (v : W ⟶ V) (u : V ⟶ P) (h : W ⟶ P) (hh : h = v ≫ u)
    (π : P ⟶ Y') (r : V ⟶ X') (q : W ⟶ X') (hq : q = v ≫ r) (f : X' ⟶ Y')
    (w : u ≫ π = r ≫ f) (w' : h ≫ π = q ≫ f)
    (M : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    tensorBaseChangeCounitApp A h q π f w' M =
      (leftDerivedUpperStarComp A v u h hh).hom.app _ ≫
        (L((v)^*[A])).map (tensorBaseChangeCounitApp A u r π f w M) ≫
        (leftDerivedUpperStarComp A v r q hq).inv.app M := by
  simp only [tensorBaseChangeCounitApp, Functor.map_comp, Category.assoc]
  rw [map_map_leftDerivedUpperStarComp_inv_app,
    map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app_assoc A v r f q
      (u ≫ π) (h ≫ π) hq w (by rw [w', hq, Category.assoc]),
    map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc A v u π h
      (u ≫ π) (h ≫ π) hh rfl (by rw [hh, Category.assoc]),
    Iso.hom_inv_id_app_assoc]

/-- The counit morphism `AlgebraicGeometry.Etale.tensorBaseChangeCounitApp` of a composite
`h = v ≫ u`, when `u` is pasted with the composite `r = u ≫ π`. -/
private lemma tensorBaseChangeCounitApp_comp_of_snd [UpperStarPreservesFlat A]
    {W V P X' Y' : Scheme.{u}} (v : W ⟶ V) (u : V ⟶ P) (h : W ⟶ P) (hh : h = v ≫ u)
    (π : P ⟶ Y') (r : V ⟶ Y') (hr : r = u ≫ π) (q : W ⟶ X') (f : X' ⟶ Y')
    (w : v ≫ r = q ≫ f) (w' : h ≫ π = q ≫ f)
    (M : _root_.DerivedCategory (Sheaf X'.smallEtaleTopology A)) :
    tensorBaseChangeCounitApp A h q π f w' M =
      (leftDerivedUpperStarComp A v u h hh).hom.app _ ≫
        (L((v)^*[A])).map ((leftDerivedUpperStarComp A u π r hr).inv.app _) ≫
        tensorBaseChangeCounitApp A v q r f w M := by
  simp only [tensorBaseChangeCounitApp]
  rw [map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app_assoc A v u π h r
      (v ≫ r) hh hr (by rw [hh, hr, Category.assoc]),
    Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarComp_inv_app_comp_hom_app_congr_assoc A h π q f (h ≫ π) (v ≫ r) rfl w'
      (by rw [hh, hr, Category.assoc]) (by rw [← w])]

/-- The Künneth map of two commutative squares `h ≫ πᵢ = qᵢ ≫ fᵢ` (`i = 1, 2`) with a common
edge `h : W ⟶ P`: for `M₁ ∈ D(X₁_ét)` and `M₂ ∈ D(X₂_ét)`, the morphism

`Lπ₁^* Rf₁_* M₁ ⊗ᴸ Lπ₂^* Rf₂_* M₂ ⟶ Rh_* (Lq₁^* M₁ ⊗ᴸ Lq₂^* M₂)`

transpose along `Lh^* ⊣ Rh_*` of the composite

`Lh^*(Lπ₁^* Rf₁_* M₁ ⊗ᴸ Lπ₂^* Rf₂_* M₂) ≅ Lh^* Lπ₁^* Rf₁_* M₁ ⊗ᴸ Lh^* Lπ₂^* Rf₂_* M₂
  ≅ Lq₁^* Lf₁^* Rf₁_* M₁ ⊗ᴸ Lq₂^* Lf₂^* Rf₂_* M₂ ⟶ Lq₁^* M₁ ⊗ᴸ Lq₂^* M₂`

of the monoidality of `Lh^*`, the composition isomorphisms through `L(h ≫ πᵢ)^* = L(qᵢ ≫ fᵢ)^*`
and the counits of `Lfᵢ^* ⊣ Rfᵢ_*` (`AlgebraicGeometry.Etale.tensorBaseChangeCounitApp`). -/
noncomputable def kunnethMapOfSquares [UpperStarPreservesFlat A] {W P X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (h : W ⟶ P) (q₁ : W ⟶ X₁) (q₂ : W ⟶ X₂) (π₁ : P ⟶ Y₁) (π₂ : P ⟶ Y₂) (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂) (w₁ : h ≫ π₁ = q₁ ≫ f₁) (w₂ : h ≫ π₂ = q₂ ≫ f₂)
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    ((-⊗ᴸ-(P)[A]).obj ((L((π₁)^*[A])).obj ((R((f₁)_*[A])).obj M₁))).obj
        ((L((π₂)^*[A])).obj ((R((f₂)_*[A])).obj M₂)) ⟶
      (R((h)_*[A])).obj (((-⊗ᴸ-(W)[A]).obj ((L((q₁)^*[A])).obj M₁)).obj
        ((L((q₂)^*[A])).obj M₂)) :=
  (derivedUpperStarLowerStarAdjunction A h).homEquiv _ _
    (((leftDerivedUpperStarTensorComparison A h).app _).app _ ≫
      ((-⊗ᴸ-(W)[A]).map (tensorBaseChangeCounitApp A h q₁ π₁ f₁ w₁ M₁)).app _ ≫
      ((-⊗ᴸ-(W)[A]).obj _).map (tensorBaseChangeCounitApp A h q₂ π₂ f₂ w₂ M₂))

/-- The Künneth map `Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)` for `f₁ : X₁ ⟶ Y₁`,
`f₂ : X₂ ⟶ Y₂` and `Yᵢ` over `S` through `bᵢ`.

Writing `h = f₁ × f₂ : X₁ ×_S X₂ ⟶ Y₁ ×_S Y₂`, `pᵢ` for the projections of `Y₁ ×_S Y₂` and `qᵢ`
for those of `X₁ ×_S X₂`, it is the transpose along `Lh^* ⊣ Rh_*` of the composite

`Lh^*(Lp₁^* Rf₁_* M₁ ⊗ᴸ Lp₂^* Rf₂_* M₂) ≅ Lh^* Lp₁^* Rf₁_* M₁ ⊗ᴸ Lh^* Lp₂^* Rf₂_* M₂
  ≅ Lq₁^* Lf₁^* Rf₁_* M₁ ⊗ᴸ Lq₂^* Lf₂^* Rf₂_* M₂ ⟶ Lq₁^* M₁ ⊗ᴸ Lq₂^* M₂`

of the monoidality of `Lh^*`, the composition isomorphisms through `L(pᵢ ∘ h)^* = L(fᵢ ∘ qᵢ)^*`
and the counits of `Lfᵢ^* ⊣ Rfᵢ_*` (`AlgebraicGeometry.Etale.kunnethMapOfSquares`). -/
noncomputable def externalProductKunnethMap [UpperStarPreservesFlat A] {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    externalProduct A b₁ b₂ ((R((f₁)_*[A])).obj M₁) ((R((f₂)_*[A])).obj M₂) ⟶
      (R((pullback.mapOverBase f₁ f₂ b₁ b₂)_*[A])).obj
        (externalProduct A (f₁ ≫ b₁) (f₂ ≫ b₂) M₁ M₂) :=
  kunnethMapOfSquares A (pullback.mapOverBase f₁ f₂ b₁ b₂) (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂))
    (pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂)) (pullback.fst b₁ b₂) (pullback.snd b₁ b₂) f₁ f₂
    (pullback.mapOverBase_fst f₁ f₂ b₁ b₂) (pullback.mapOverBase_snd f₁ f₂ b₁ b₂) M₁ M₂

/-- The Künneth map of two squares with common edge `h = v ≫ u` is the composite
`E₁ ≫ Ru_* E₂ ≫ (Ru_* Rv_* ≅ Rh_*)` of any two morphisms `E₁`, `E₂` whose transposes along
`Lu^* ⊣ Ru_*` and `Lv^* ⊣ Rv_*` are the composites `hE₁` and `hE₂` of tensor comparisons and
counit morphisms. -/
private lemma kunnethMapOfSquares_eq_comp [UpperStarPreservesFlat A]
    {W V P X₁ X₂ Y₁ Y₂ : Scheme.{u}} (v : W ⟶ V) (u : V ⟶ P) (h : W ⟶ P) (hh : v ≫ u = h)
    (π₁ : P ⟶ Y₁) (π₂ : P ⟶ Y₂) (r₁ : V ⟶ X₁) (r₂ : V ⟶ Y₂) (q₁ : W ⟶ X₁) (q₂ : W ⟶ X₂)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (hr₂ : r₂ = u ≫ π₂) (hq₁ : q₁ = v ≫ r₁)
    (w₁ : u ≫ π₁ = r₁ ≫ f₁) (w₂ : v ≫ r₂ = q₂ ≫ f₂) (w₁' : h ≫ π₁ = q₁ ≫ f₁)
    (w₂' : h ≫ π₂ = q₂ ≫ f₂)
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A))
    (E₁ : ((-⊗ᴸ-(P)[A]).obj ((L((π₁)^*[A])).obj ((R((f₁)_*[A])).obj M₁))).obj
        ((L((π₂)^*[A])).obj ((R((f₂)_*[A])).obj M₂)) ⟶
      (R((u)_*[A])).obj (((-⊗ᴸ-(V)[A]).obj ((L((r₁)^*[A])).obj M₁)).obj
        ((L((r₂)^*[A])).obj ((R((f₂)_*[A])).obj M₂))))
    (E₂ : ((-⊗ᴸ-(V)[A]).obj ((L((r₁)^*[A])).obj M₁)).obj
        ((L((r₂)^*[A])).obj ((R((f₂)_*[A])).obj M₂)) ⟶
      (R((v)_*[A])).obj (((-⊗ᴸ-(W)[A]).obj ((L((q₁)^*[A])).obj M₁)).obj
        ((L((q₂)^*[A])).obj M₂)))
    (hE₁ : (L((u)^*[A])).map E₁ ≫ (derivedUpperStarLowerStarAdjunction A u).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A u).app _).app _ ≫
        ((-⊗ᴸ-(V)[A]).map (tensorBaseChangeCounitApp A u r₁ π₁ f₁ w₁ M₁)).app _ ≫
        ((-⊗ᴸ-(V)[A]).obj _).map ((leftDerivedUpperStarComp A u π₂ r₂ hr₂).inv.app _))
    (hE₂ : (L((v)^*[A])).map E₂ ≫ (derivedUpperStarLowerStarAdjunction A v).counit.app _ =
      ((leftDerivedUpperStarTensorComparison A v).app _).app _ ≫
        ((-⊗ᴸ-(W)[A]).obj _).map (tensorBaseChangeCounitApp A v q₂ r₂ f₂ w₂ M₂) ≫
        ((-⊗ᴸ-(W)[A]).map ((leftDerivedUpperStarComp A v r₁ q₁ hq₁).inv.app M₁)).app _) :
    kunnethMapOfSquares A h q₁ q₂ π₁ π₂ f₁ f₂ w₁' w₂' M₁ M₂ =
      E₁ ≫ (R((u)_*[A])).map E₂ ≫ (rightDerivedLowerStarCompIsoOfComp A v u h hh).hom.app _ := by
  subst hh
  apply ((derivedUpperStarLowerStarAdjunction A (v ≫ u)).homEquiv _ _).symm.injective
  rw [kunnethMapOfSquares, Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp,
    Functor.map_comp,
    Category.assoc, Category.assoc, map_rightDerivedLowerStarCompIsoOfComp_hom_app_comp_counit,
    map_leftDerivedUpperStarComp_hom_app_assoc, map_leftDerivedUpperStarComp_hom_app_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    map_map_derivedUpperStarLowerStarAdjunction_counit, ← Category.assoc ((L((u)^*[A])).map E₁),
    Functor.map_comp,
    Category.assoc, hE₂, hE₁, Functor.map_comp, Functor.map_comp,
    tensorBaseChangeCounitApp_comp_of_fst A v u (v ≫ u) rfl π₁ r₁ q₁ hq₁ f₁ w₁ w₁',
    tensorBaseChangeCounitApp_comp_of_snd A v u (v ≫ u) rfl π₂ r₂ hr₂ q₂ f₂ w₂ w₂']
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc,
    derivedTensor_map_app_comp_obj_map, derivedTensor_map_app_comp_obj_map_assoc,
    leftDerivedUpperStarTensorComparison_comp_derivedTensor_comp,
    leftDerivedUpperStarTensorComparison_naturality_right_assoc,
    leftDerivedUpperStarTensorComparison_naturality_left_assoc]

/-- The Künneth map `Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)` is the composite of the Künneth
maps with one identity factor for `f₁`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarMap`) and for `f₂`
(`AlgebraicGeometry.Etale.externalProductRightDerivedLowerStarSndMap`), along the factorisation
`f₁ × f₂ = (f₁ × 𝟙) ∘ (𝟙 × f₂)`, and of the composition isomorphism of direct images. -/
lemma externalProductKunnethMap_eq [UpperStarPreservesFlat A] {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (M₁ : _root_.DerivedCategory (Sheaf X₁.smallEtaleTopology A))
    (M₂ : _root_.DerivedCategory (Sheaf X₂.smallEtaleTopology A)) :
    externalProductKunnethMap A b₁ b₂ f₁ f₂ M₁ M₂ =
      externalProductRightDerivedLowerStarMap A b₁ b₂ f₁ M₁ ((R((f₂)_*[A])).obj M₂) ≫
        (R((pullback.mapOverBaseRight f₁ b₁ b₂)_*[A])).map
          (externalProductRightDerivedLowerStarSndMap A (f₁ ≫ b₁) b₂ f₂ M₁ M₂) ≫
        (rightDerivedLowerStarCompIsoOfComp A
          (pullback.map (f₁ ≫ b₁) (f₂ ≫ b₂) (f₁ ≫ b₁) b₂ (𝟙 X₁) f₂ (𝟙 S) (by simp) (by simp))
          (pullback.mapOverBaseRight f₁ b₁ b₂) (pullback.mapOverBase f₁ f₂ b₁ b₂)
          (by ext <;> simp)).hom.app _ := by
  exact kunnethMapOfSquares_eq_comp A
    (pullback.map (f₁ ≫ b₁) (f₂ ≫ b₂) (f₁ ≫ b₁) b₂ (𝟙 X₁) f₂ (𝟙 S) _ _)
    (pullback.mapOverBaseRight f₁ b₁ b₂) (pullback.mapOverBase f₁ f₂ b₁ b₂) _
    (pullback.fst b₁ b₂) (pullback.snd b₁ b₂) (pullback.fst (f₁ ≫ b₁) b₂)
    (pullback.snd (f₁ ≫ b₁) b₂)
    (pullback.fst (f₁ ≫ b₁) (f₂ ≫ b₂)) (pullback.snd (f₁ ≫ b₁) (f₂ ≫ b₂)) f₁ f₂ _ _ _ _ _ _ M₁ M₂
    (externalProductRightDerivedLowerStarMap A b₁ b₂ f₁ M₁ ((R((f₂)_*[A])).obj M₂))
    (externalProductRightDerivedLowerStarSndMap A (f₁ ≫ b₁) b₂ f₂ M₁ M₂)
    (map_externalProductRightDerivedLowerStarMap_comp_counit A b₁ b₂ f₁ M₁ _)
    (map_externalProductRightDerivedLowerStarSndMap_comp_counit A (f₁ ≫ b₁) b₂ f₂ M₁ M₂)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- The ordinary Künneth formula with an identity first factor: over a field `k`, for a finite
ring `Λ` whose exponent is invertible in `k` and morphisms `c : Z ⟶ Spec k`, `b : Y ⟶ Spec k`
and `f : X ⟶ Y` of finite type, the comparison `Q ⊠ Rf_* M ⟶ R(𝟙_Z × f)_* (Q ⊠ M)` is an
isomorphism for all `Q ∈ D(Z_ét, Λ)` and `M ∈ D(X_ét, Λ)`. -/
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
  exact IsIso.comp_isIso' this (Iso.isIso_hom
    ((R((pullback.map c (f ≫ b) c b (𝟙 Z) f (𝟙 _) (by simp)
      (by simp))_*[ModuleCat.{u + 1} Λ])).mapIso
      (((-⊗ᴸ-(pullback c (f ≫ b))[ModuleCat.{u + 1} Λ]).mapIso
        ((leftDerivedUpperStarComp _ _ _ _ (by simp)).app Q).symm).app _)))

/-- **Ordinary external Künneth**. Let `k` be a field, `Λ` a finite ring whose exponent
is invertible in `k`, and `f₁ : X₁ ⟶ Y₁`, `f₂ : X₂ ⟶ Y₂` morphisms of `k`-schemes of finite type
(with structure morphisms `bᵢ : Yᵢ ⟶ Spec k`, and `Xᵢ` over `k` through `fᵢ ≫ bᵢ`). Then for
`M₁ ∈ D(X₁,ét, Λ)` and `M₂ ∈ D(X₂,ét, Λ)` the Künneth map
(`AlgebraicGeometry.Etale.externalProductKunnethMap`, the transpose of `ε_{f₁} ⊠ ε_{f₂}`)

`Rf₁_* M₁ ⊠ Rf₂_* M₂ ⟶ R(f₁ × f₂)_* (M₁ ⊠ M₂)`

is an isomorphism. -/
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
  rw [externalProductKunnethMap_eq]
  infer_instance

end Etale

end AlgebraicGeometry
