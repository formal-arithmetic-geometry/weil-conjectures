/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonCounit

/-!
# Unit compatibility of the comparison of direct images

For a morphism of schemes `g : X ⟶ Y`, let `c_g : ν_Y^* Rg_* ⟶ Rg_* ν_X^*` be the comparison
of bounded below direct images (`fixedComparisonDirectImageMatePlus`) and
`β_g : g^* ν_Y^* ≅ ν_X^* g^*` the comparison of inverse images
(`fixedComparisonPullbackPlus`). We show that `ν_Y^*` of the étale unit followed by `c_g`
equals the pro-étale unit followed by `Rg_*(β_g)`. It is deduced from the counit version
`fixedComparisonDirectImageMatePlus_counit`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Unit compatibility of the comparison of direct images: for `L ∈ D⁺(Y_ét, Λ)`, the composite
`ν_Y^* L ⟶ ν_Y^* Rg_* g^* L ⟶ Rg_* ν_X^* g^* L` of `ν_Y^*` of the étale unit with `c_g` equals
the pro-étale unit `ν_Y^* L ⟶ Rg_* g^* ν_Y^* L` followed by `Rg_*(β_g)`:
```
ν_Y^* L ────────────→ ν_Y^* Rg_* g^* L
   │                        │ c_g
   ↓                        ↓
Rg_* g^* ν_Y^* L ──────→ Rg_* ν_X^* g^* L
           Rg_*(β_g)
```
-/
theorem fixedComparisonDirectImageMatePlus_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).unit.app L) ≫
      (fixedComparisonDirectImageMatePlus Λ g).app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L) =
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g).unit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).mapDerivedCategoryPlus.obj L) ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).rightDerivedFunctorPlus.map
          ((fixedComparisonPullbackPlus Λ g).inv.app L) := by
  let adj := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g
  let adjE := Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) g
  let β := fixedComparisonPullbackPlus Λ g
  apply (adj.homEquiv _ _).symm.injective
  have hc : (upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus Λ g).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) ≫
      adj.counit.app ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) =
      β.inv.app _ ≫ (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).mapDerivedCategoryPlus.map
        (adjE.counit.app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).mapDerivedCategoryPlus.obj L)) := by
    rw [← fixedComparisonDirectImageMatePlus_counit]
    exact (β.inv_hom_id_app_assoc _ _).symm
  simp only [Adjunction.homEquiv_counit, Functor.id_obj]
  erw [Functor.map_comp, Category.assoc, hc]
  rw [Functor.map_comp, Category.assoc, adj.counit_naturality, adj.left_triangle_components_assoc]
  have hβ := β.inv.naturality (adjE.unit.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hβ
  rw [← Category.assoc, hβ, Category.assoc, ← Functor.map_comp]
  erw [adjE.left_triangle_components]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale
