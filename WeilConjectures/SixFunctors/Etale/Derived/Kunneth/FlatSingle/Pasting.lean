/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.TensorBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# The base change map for a pushforward tensored with a complex: unit and pasting

For a commutative square `h ≫ f' = e ≫ g` of schemes, the base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`)

`M ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* M ⊗ᴸ Le^* F)`

is, at the unit `M = Λ`, the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap`), up to the unitors
(`AlgebraicGeometry.Etale.tensorBaseChangeMap_tensorUnit`). For two squares pasted horizontally,
the base change map of the outer square is the base change map of the right square followed by
the base change map of the left square (`AlgebraicGeometry.Etale.tensorBaseChangeMap_paste`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  [HasSmallSiteSheafify A]

/-- The morphism `Lh^* Lf'^* Rg_* F ⟶ Le^* F` of the base change map for a pushforward tensored
with a complex is the transpose of the derived base change map `Lf'^* Rg_* F ⟶ Rh_* Le^* F`. -/
lemma tensorBaseChangeCounitApp_eq {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeCounitApp A h e f' g w F =
      L((h)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk w.symm)).app F) ≫
        (derivedUpperStarLowerStarAdjunction A h).counit.app _ := by
  sorry

/-- **The base change map at the unit**: for a commutative square `h ≫ f' = e ≫ g`, the base change
map `Λ ⊗ᴸ Lf'^* Rg_* F ⟶ Rh_* (Lh^* Λ ⊗ᴸ Le^* F)` is the derived base change map
`Lf'^* Rg_* F ⟶ Rh_* Le^* F`, up to the left unitors and the identification `Lh^* Λ ≅ Λ`. -/
lemma tensorBaseChangeMap_tensorUnit {X' S' T Y : Scheme.{u}} (h : Y ⟶ X') (e : Y ⟶ T)
    (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h e f' g w (𝟙_ _) F ≫
        R((h)_*[A]).map ((leftDerivedUpperStarUnitIso A h).hom ▷ L((e)^*[A]).obj F ≫
          (λ_ _).hom) =
      (λ_ _).hom ≫ (derivedBaseChangeMap A (CommSq.mk w.symm)).app F := by
  sorry

/-- **Pasting of base change maps**: for two commutative squares pasted horizontally,

```
  Y --e₁--> T₁ --e₂--> T
  |         |          |
  h         g₁         g
  v         v          v
  X' --a--> S₁ --b---> S'
```

the base change map of the outer square at `(M, F)`, followed by `Le₁^* Le₂^* ≅ L(e₁ ≫ e₂)^*`, is
`M ⊗ᴸ -` applied to `L(a ≫ b)^* ≅ La^* Lb^*` and to `La^*` of the derived base change map
`Lb^* Rg_* F ⟶ Rg₁_* Le₂^* F` of the right square, followed by the base change map of the left
square at `(M, Le₂^* F)`. -/
lemma tensorBaseChangeMap_paste {X' S₁ S' T₁ T Y : Scheme.{u}} (h : Y ⟶ X') (e₁ : Y ⟶ T₁)
    (a : X' ⟶ S₁) (g₁ : T₁ ⟶ S₁) (wL : h ≫ a = e₁ ≫ g₁) (e₂ : T₁ ⟶ T) (b : S₁ ⟶ S')
    (g : T ⟶ S') (wR : g₁ ≫ b = e₂ ≫ g) (w : h ≫ a ≫ b = (e₁ ≫ e₂) ≫ g)
    (M : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (F : DerivedCategory (Sheaf T.smallEtaleTopology A)) :
    tensorBaseChangeMap A h (e₁ ≫ e₂) (a ≫ b) g w M F ≫
        R((h)_*[A]).map (((-⊗ᴸ-(Y)[A]).obj (L((h)^*[A]).obj M)).map
          ((leftDerivedUpperStarComp A e₁ e₂).hom.app F)) =
      ((-⊗ᴸ-(X')[A]).obj M).map ((leftDerivedUpperStarComp A a b).hom.app (R((g)_*[A]).obj F) ≫
          L((a)^*[A]).map ((derivedBaseChangeMap A (CommSq.mk wR.symm)).app F)) ≫
        tensorBaseChangeMap A h e₁ a g₁ wL M (L((e₂)^*[A]).obj F) := by
  sorry

end Etale

end AlgebraicGeometry
