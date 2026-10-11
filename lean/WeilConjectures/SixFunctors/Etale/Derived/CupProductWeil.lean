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
(`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange`).
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
  [HasSmallSiteSheafify A] [Etale.UpperStarPreservesFlat A]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

namespace Etale

variable {X Y : Scheme.{u}} {a : X ⟶ Y} [HasCompactification a] {g : X ⟶ X} {h : Y ⟶ Y}

/-- **The mixed-support cup product is compatible with exchange maps**: for an exchange map `Ex`
compatible with the projection maps (hypothesis `hEx`), the cup product intertwines
`Ex ≫ Ra_!(φ ⊗ ψ)` and `(Ex ≫ Ra_! φ) ⊗ (Ex_* ≫ Ra_* ψ)`. -/
theorem mixedSupportCupProduct_exchange (sq : CommSq g a a h)
    (Ex : R(a)_![A] ⋙ L((h)^*[A]) ⟶ L((g)^*[A]) ⋙ R(a)_![A])
    (hEx : ∀ (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
      (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)),
      L((h)^*[A]).map (((projectionMap A a).app K).app M) ≫
          Ex.app (((derivedTensor A X).obj K).obj (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((leftDerivedUpperStarTensorComparison A g).app K).app
            (L((a)^*[A]).obj M)) ≫
          (R(a)_![A]).map (((derivedTensor A X).obj (L((g)^*[A]).obj K)).map
            (derivedSquareUpperStarIsoInvApp A sq M)) =
        ((leftDerivedUpperStarTensorComparison A h).app ((R(a)_![A]).obj K)).app M ≫
          ((derivedTensor A Y).map (Ex.app K)).app (L((h)^*[A]).obj M) ≫
          ((projectionMap A a).app (L((g)^*[A]).obj K)).app (L((h)^*[A]).obj M))
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (φ : (L((g)^*[A])).obj K ⟶ K) (ψ : (L((g)^*[A])).obj L ⟶ L) :
    (L((h)^*[A])).map (mixedSupportCupProduct A a K L) ≫
        (Ex.app (((derivedTensor A X).obj K).obj L) ≫
          (R(a)_![A]).map ((leftDerivedUpperStarTensorIso A g K L).hom ≫
            ((derivedTensor A X).map φ).app _ ≫ ((derivedTensor A X).obj K).map ψ)) =
      ((leftDerivedUpperStarTensorIso A h ((R(a)_![A]).obj K) ((R((a)_*[A])).obj L)).hom ≫
          ((derivedTensor A Y).map (Ex.app K ≫ (R(a)_![A]).map φ)).app _ ≫
          ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map
            ((derivedBaseChangeMap A sq).app L ≫ (R((a)_*[A])).map ψ)) ≫
        mixedSupportCupProduct A a K L := by
  sorry

end Etale

end AlgebraicGeometry
