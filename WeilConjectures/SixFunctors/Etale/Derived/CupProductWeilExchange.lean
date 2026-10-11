/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# The mixed-support cup product and exchange maps: the proof

Proof of the compatibility of the mixed-support cup product with exchange maps, stated as
`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange'` with the same statement as
`AlgebraicGeometry.Etale.mixedSupportCupProduct_exchange`.
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

omit [HasSmallSiteSheafify A] in
/-- Naturality of the mixed-support cup product in both variables. -/
set_option maxHeartbeats 2000000 in
lemma mixedSupportCupProduct_naturality {K K' L L' : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (φ : K' ⟶ K) (ψ : L' ⟶ L) :
    ((derivedTensor A Y).map ((R(a)_![A]).map φ)).app ((R((a)_*[A])).obj L') ≫
        ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map ((R((a)_*[A])).map ψ) ≫
        mixedSupportCupProduct A a K L =
      mixedSupportCupProduct A a K' L' ≫
        (R(a)_![A]).map (((derivedTensor A X).map φ).app _ ≫
          ((derivedTensor A X).obj K).map ψ) := by
  have h₁ : ((derivedTensor A Y).obj ((R(a)_![A]).obj K)).map ((R((a)_*[A])).map ψ) ≫
      ((projectionMap A a).app K).app ((R((a)_*[A])).obj L) =
      ((projectionMap A a).app K).app ((R((a)_*[A])).obj L') ≫
        (R(a)_![A]).map (((derivedTensor A X).obj K).map
          ((L((a)^*[A])).map ((R((a)_*[A])).map ψ))) :=
    ((projectionMap A a).app K).naturality _
  have h₂ : ((derivedTensor A Y).map ((R(a)_![A]).map φ)).app ((R((a)_*[A])).obj L') ≫
      ((projectionMap A a).app K).app ((R((a)_*[A])).obj L') =
      ((projectionMap A a).app K').app ((R((a)_*[A])).obj L') ≫
        (R(a)_![A]).map (((derivedTensor A X).map φ).app
          ((L((a)^*[A])).obj ((R((a)_*[A])).obj L'))) :=
    NatTrans.congr_app ((projectionMap A a).naturality φ) _
  have h₃ := (derivedUpperStarLowerStarAdjunction A a).counit.naturality ψ
  dsimp at h₃
  simp only [mixedSupportCupProduct, reassoc_of% h₁, reassoc_of% h₂, Category.assoc,
    ← Functor.map_comp]
  congr 2
  rw [h₃, Functor.map_comp, ← NatTrans.naturality_assoc]

end Etale

end AlgebraicGeometry
