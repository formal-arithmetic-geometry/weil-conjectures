/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-! # Composition of the coefficient comparisons in target transitions

Source: Stacks Tags 0F07 and 09Z1, canonical restriction comparisons.
(blueprint: lem-sbc-pullback-comparison-comp)
-/

@[expose] public section

universe u
open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pullback and single-complex comparisons for two commutative squares compose.

Source: Stacks Tag 0F07, condition (1), and Tag 09Z1, the canonical restriction maps.
(blueprint: lem-sbc-pullback-comparison-comp)

Proof: write each square comparison as the inverse composition comparison for its
upper-left path followed by the comparison for its lower-right path. Apply associativity
of the derived pullback comparisons to the triples (a₁,a₂,e), (a₁,e₂,π₂), and
(e₁,π₁,π₂). Naturality moves the identification π₂^*(F[0]) → (π₂^*F)[0]
past the (a₁,e₂) comparison. The intermediate comparison and its inverse cancel.
For the remaining coefficient maps, composition of the exact functors π₂^* and π₁^*
commutes with placing a sheaf in degree zero: on a single complex both maps are the
underived composition comparison in degree zero and the unique zero maps elsewhere.
The localization factorization and the fully faithful inclusion D⁺ → D preserve this
identity. After applying e₁^*, this identifies the two single-complex maps followed by
(π₁^*π₂^*F)[0] → ((π₁ ≫ π₂)^*F)[0] with the single-complex comparison for π₁ ≫ π₂.
The uncancelled source comparison is precisely the inverse comparison for a₁,a₂.
This uses only commutativity of the two squares, not cartesianness; identity arrows and
zero sheaves give the same identities by the unit laws.
-/
theorem Etale.baseChangePullbackComparison_comp
    {T Y T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e : Y ⟶ T)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂)
    (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let c₂ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₂ e).inv.app K ≫
      eqToHom (by rw [wa₂]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₂ π₂).hom.app K ≫
      D+((e₂)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    let c₁ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ e₂).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      eqToHom (by rw [wa₁]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ π₁).hom.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₁)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
          (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F))
    let c₀ := (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) (a₁ ≫ a₂) e).inv.app K ≫
      eqToHom (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc]) ≫
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) e₁ (π₁ ≫ π₂)).hom.app K ≫
      D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
        ((((π₁ ≫ π₂)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
    D+((a₁)^*[ModuleCat.{u + 1} Λ]).map c₂ ≫ c₁ ≫
        D+((e₁)^*[ModuleCat.{u + 1} Λ]).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F)) =
      (Etale.upperStarPlusComp (ModuleCat.{u + 1} Λ) a₁ a₂).inv.app
          (D+((e)^*[ModuleCat.{u + 1} Λ]).obj K) ≫ c₀ := by sorry

end AlgebraicGeometry
