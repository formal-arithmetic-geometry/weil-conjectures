/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalIso

/-!
# Extension of scalars commutes with pullback compatibly with the unit comparisons

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings, `F = Λ' ⊗_Λ -` the extension of scalars
of étale sheaves and `e : U ⟶ X` a morphism of schemes. The monoidal commutation
`F_X ⋙ e^* ≅ e^* ⋙ F_U` (`AlgebraicGeometry.Etale.extendScalarsUpperStarIso`) induces on
homotopy categories an isomorphism compatible with the unit comparisons
(`AlgebraicGeometry.Etale.extendScalarsUpperStarHomotopyIso_inv_app_unit_comp_η`).
We also describe the unit comparison of the derived pullback through the counit
(`AlgebraicGeometry.Etale.leftDerivedUpperStarOplaxMonoidal_η_comp_ε`).

The instances of the generic lemmas are compared with those of the étale sheaf categories by the
kernel slowly (about ten seconds per comparison): each instance of a generic lemma is stated as a
separate lemma, so that the comparison is made only once.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {U X : Scheme.{u}}
  (e : U ⟶ X)

/-- The unit comparison of `(F_X ⋙ e^*)` on homotopy categories is that of `F_X` followed by that
of `e^*` (`CategoryTheory.Functor.mapHomotopyCategory_map_η_comp_η`, stated separately so that
the kernel compares the instances of the homotopy categories only once). -/
lemma mapHomotopyCategory_map_η_comp_η_extendScalars_upperStar :
    (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) ≫
      η (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)) =
    η ((Sheaf.extendScalars X.smallEtaleTopology ρ ⋙
      (e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)) :=
  Functor.mapHomotopyCategory_map_η_comp_η _ _

/-- The unit comparison of `(e^* ⋙ F_U)` on homotopy categories is that of `e^*` followed by that
of `F_U`. -/
lemma mapHomotopyCategory_map_η_comp_η_upperStar_extendScalars :
    ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) ≫
      η ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) =
    η (((e)^*[ModuleCat.{u + 1} Λ] ⋙
      Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) :=
  Functor.mapHomotopyCategory_map_η_comp_η _ _

/-- The monoidal isomorphism `F_X ⋙ e^* ≅ e^* ⋙ F_U` is compatible with the unit comparisons on
homotopy categories. -/
lemma natTransMapHomotopyCategory_extendScalarsUpperStarIso_inv_app_unit_comp_η :
    (NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).inv (.up ℤ)).app (𝟙_ _) ≫
      η ((Sheaf.extendScalars X.smallEtaleTopology ρ ⋙
        (e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)) =
    η (((e)^*[ModuleCat.{u + 1} Λ] ⋙
      Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) := by
  have := isMonoidal_extendScalarsUpperStarIso_inv ρ e
  exact Functor.natTransMapHomotopyCategory_app_unit_comp_η _

/-- The commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U` on homotopy categories is compatible with the unit
comparisons. -/
lemma extendScalarsUpperStarHomotopyIso_inv_app_unit_comp_η :
    (extendScalarsUpperStarHomotopyIso ρ e).inv.app (𝟙_ _) ≫
        (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)).map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) ≫
        η (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)) =
      ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
          (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) ≫
        η ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) := by
  simp only [extendScalarsUpperStarHomotopyIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app,
    Category.id_comp, Category.assoc]
  exact (whisker_eq _ (mapHomotopyCategory_map_η_comp_η_extendScalars_upperStar ρ e)).trans
    ((natTransMapHomotopyCategory_extendScalarsUpperStarIso_inv_app_unit_comp_η ρ e).trans
      (mapHomotopyCategory_map_η_comp_η_upperStar_extendScalars ρ e).symm)

variable (Λ) in
/-- The unit comparison of the derived pullback `Le^*`, through the unit comparisons of the
localization functors and the counit of `Le^*` at the unit. -/
lemma leftDerivedUpperStarOplaxMonoidal_η_comp_ε :
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    η L((e)^*[ModuleCat.{u + 1} Λ]) ≫ ε DerivedCategory.Qh =
      L((e)^*[ModuleCat.{u + 1} Λ]).map (ε DerivedCategory.Qh) ≫
        ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app (𝟙_ _) ≫
          DerivedCategory.Qh.map
            (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  refine (?_ : (L((e)^*[ModuleCat.{u + 1} Λ]).map (ε DerivedCategory.Qh) ≫
      ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (ε DerivedCategory.Qh)) ≫ ε DerivedCategory.Qh = _)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Etale
