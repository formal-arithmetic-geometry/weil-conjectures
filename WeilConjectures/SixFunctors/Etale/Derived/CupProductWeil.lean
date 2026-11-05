/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# The mixed-support cup product and exchange maps

For a commutative square `g ≫ a = a ≫ h` and any exchange map `Ex : Ra_! ⋙ Lh^* ⟶ Lg^* ⋙ Ra_!`
compatible with the projection maps, the mixed-support cup product
`Ra_! K ⊗ᴸ Ra_* L ⟶ Ra_!(K ⊗ᴸ L)` intertwines the data induced by `Ex`, the derived base change
map `Ex_*` and Weil data `φ`, `ψ`
(`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange`). The proof goes through the general form
`AlgebraicGeometry.Etale.projectionMap_exchange`, where the counit `La^* Ra_* L ⟶ L` is replaced by
any morphism `La^* M ⟶ L`.
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
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y : Scheme.{u}} {a : X ⟶ Y} [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

variable (a) in
/-- Naturality of the projection map `Ra_!K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^*M)` in `K`. -/
@[reassoc]
lemma projectionMap_naturality_left {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (φ : K ⟶ K') (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensor A Y).map ((R(a)_![A]).map φ)).app M ≫ ((projectionMap A a).app K').app M =
      ((projectionMap A a).app K).app M ≫
        (R(a)_![A]).map (((derivedTensor A X).map φ).app ((L((a)^*[A])).obj M)) :=
  congr_app ((projectionMap A a).naturality φ) M

variable (a) in
/-- Naturality of the projection map `Ra_!K ⊗ᴸ M ⟶ Ra_!(K ⊗ᴸ La^*M)` in `M`. -/
@[reassoc]
lemma projectionMap_naturality_right (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {M M' : DerivedCategory (Sheaf Y.smallEtaleTopology A)} (u : M ⟶ M') :
    ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map u ≫ ((projectionMap A a).app K).app M' =
      ((projectionMap A a).app K).app M ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map ((L((a)^*[A])).map u)) :=
  ((projectionMap A a).app K).naturality u

end Etale

end AlgebraicGeometry
