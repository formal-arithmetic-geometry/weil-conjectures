/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalIso

/-!
# The commutation of the reduction of coefficients with the derived pullback preserves the units
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) {U X : Scheme.{u}}
  (e : U ⟶ X)

variable (ρ) in
lemma extendScalarsUpperStarHomotopyIso_inv_app_unit_comp_η :
    (extendScalarsUpperStarHomotopyIso ρ e).inv.app (𝟙_ _) ≫
        (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)).map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) ≫
        η (((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ)) =
      ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
          (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) ≫
        η ((Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)) := by
  have h1 := Functor.mapHomotopyCategory_map_η_comp_η (Sheaf.extendScalars X.smallEtaleTopology ρ)
    ((e)^*[ModuleCat.{u + 1} Λ'])
  have h2 := Functor.mapHomotopyCategory_map_η_comp_η ((e)^*[ModuleCat.{u + 1} Λ])
    (Sheaf.extendScalars U.smallEtaleTopology ρ)
  have := isMonoidal_extendScalarsUpperStarIso_inv ρ e
  have h3 :=
    Functor.natTransMapHomotopyCategory_app_unit_comp_η (extendScalarsUpperStarIso ρ e).inv
  rw [h1, h2, ← h3]
  simp only [extendScalarsUpperStarHomotopyIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Functor.mapHomotopyCategoryCompIso_refl_inv_app,
    Category.id_comp, Category.assoc]

variable (Λ) in
/-- The unit comparison of the derived pullback `Le^*`, through the unit comparisons of the
localization functors and the counit of `Le^*` at the unit. -/
lemma leftDerivedUpperStarOplaxMonoidal_η_comp_ε :
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    η L((e)^*[ModuleCat.{u + 1} Λ]) ≫ ε DerivedCategory.Qh =
      L((e)^*[ModuleCat.{u + 1} Λ]).map (ε DerivedCategory.Qh) ≫
        ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app (𝟙_ _) ≫
          DerivedCategory.Qh.map (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) := by
  have := DerivedCategory.isIso_ε_Qh (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  refine (?_ : (L((e)^*[ModuleCat.{u + 1} Λ]).map (ε DerivedCategory.Qh) ≫
      ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))) ≫
          CategoryTheory.inv (ε DerivedCategory.Qh)) ≫ ε DerivedCategory.Qh = _)
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- **The commutation of `Ψ` with the derived pullback preserves the units**:
`Ψ_U Le^* Λ_X ⟶ Le^* Ψ_X Λ_X ⟶ Le^* Λ'_X ⟶ Λ'_U` is `Ψ_U Le^* Λ_X ⟶ Ψ_U Λ_U ⟶ Λ'_U`. -/
lemma derivedExtendScalarsPullbackOfCounit_app_unit_comp_η :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
    letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    letI := (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
    (derivedExtendScalarsPullbackOfCounit hρ ha e).app (𝟙_ _) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          (η (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor) ≫
        η L((e)^*[ModuleCat.{u + 1} Λ']) =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (η L((e)^*[ModuleCat.{u + 1} Λ])) ≫
        η (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor := by
  sorry

end AlgebraicGeometry.Etale
