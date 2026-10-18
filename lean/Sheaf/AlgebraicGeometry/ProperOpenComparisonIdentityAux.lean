/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module
public import Sheaf.AlgebraicGeometry.ProperOpenComparison
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale
/-- The identity comparison reduces to the unit-counit cancellation for the explicit
proper-open identification. The proof expands the identification and applies the
unit-counit and identity base-change coherence laws.
Source: blueprint lem-weil-pbc-proper-open-comparison-composition.
(blueprint: lem-weil-pbc-proper-open-comparison-identity-aux). -/
theorem properOpenComparison_id_aux (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T X : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
      (properOpenIdentification Λ (𝟙 T) j j (Category.comp_id j) K).inv ≫
      (derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
        (ModuleCat.{u + 1} Λ) j).counit.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) (𝟙 T)).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)) ≫
      (lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) T).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) =
    𝟙 ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K) := by
  sorry
end AlgebraicGeometry.Etale
