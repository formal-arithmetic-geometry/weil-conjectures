/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionConstantComplex

/-!
# The canonical maps `Λ ⟶ Res Λ'` and the pullbacks

The compatibility of the canonical maps `Λ ⟶ Res Λ'` of the homotopy categories
(`AlgebraicGeometry.Etale.homotopyUnitRestrictScalars`) with the pullback along `t : X ⟶ S`
(`AlgebraicGeometry.Etale.HomotopyUnitRestrictScalarsCompat`), and the form of the commutation
`Lt^* Res ≅ Res Lt^*` at the constant complex used to compare the transposes of the counits
`Ψ Λ ≅ Λ'` (`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_hom_app_unit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'}

section Pullback

variable {X S : Scheme.{u}} (t : X ⟶ S)

set_option maxHeartbeats 800000 in
-- the kernel compares the units of the monoidal homotopy categories
variable (ρ) in
/-- The compatibility of the canonical maps `Λ ⟶ Res Λ'` of the homotopy categories
(`homotopyUnitRestrictScalars`) with the pullback along `t`, through `t^* Res ≅ Res t^*`. -/
def HomotopyUnitRestrictScalarsCompat : Prop :=
  ((t)^*[ModuleCat.{u + 1} Λ].mapHomotopyCategory (.up ℤ)).map
      (homotopyUnitRestrictScalars ρ S) ≫
    mapHomotopyCategoryUpperStarRestrictScalars ρ t (𝟙_ _) ≫
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
      (η ((t)^*[ModuleCat.{u + 1} Λ'].mapHomotopyCategory (.up ℤ))) =
  η ((t)^*[ModuleCat.{u + 1} Λ].mapHomotopyCategory (.up ℤ)) ≫ homotopyUnitRestrictScalars ρ X

variable (ρ) in
/-- The commutation `Lt^* Res ≅ Res Lt^*` at the constant complex `Λ'_S`, transported to
`Qh(Λ')` and composed with the counit of `Lt^*`, is induced by `t^* Res ≅ Res t^*`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app_unit :
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (L((t)^*[ModuleCat.{u + 1} Λ])).map ((Sheaf.derivedRestrictScalars _ ρ).map
        (inv (ε (DerivedCategory.Qh (C := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')))))) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((L((t)^*[ModuleCat.{u + 1} Λ'])).map (ε DerivedCategory.Qh)) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((t)^*[ModuleCat.{u + 1} Λ'].leftDerivedFunctorCounit.app _) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app _ =
      (L((t)^*[ModuleCat.{u + 1} Λ])).map
        ((Sheaf.restrictScalars S.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app _) ≫
      (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.app _ ≫
      DerivedCategory.Qh.map (mapHomotopyCategoryUpperStarRestrictScalars ρ t _) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  have hι' : (L((t)^*[ModuleCat.{u + 1} Λ])).map ((Sheaf.derivedRestrictScalars _ ρ).map
        (inv (ε (DerivedCategory.Qh (C := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')))))) ≫
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((L((t)^*[ModuleCat.{u + 1} Λ'])).map (ε DerivedCategory.Qh)) =
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app (DerivedCategory.Qh.obj _) := by
    have hn : (L((t)^*[ModuleCat.{u + 1} Λ])).map ((Sheaf.derivedRestrictScalars _ ρ).map
        (inv (ε (DerivedCategory.Qh (C := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')))))) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app _ =
        (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app (DerivedCategory.Qh.obj _) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          ((L((t)^*[ModuleCat.{u + 1} Λ'])).map (inv (ε (DerivedCategory.Qh
            (C := Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')))))) :=
      (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.naturality _
    rw [reassoc_of% hn, ← Functor.map_comp, ← Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [reassoc_of% hι']
  exact leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj ρ t _

end Pullback

end Etale

end AlgebraicGeometry
