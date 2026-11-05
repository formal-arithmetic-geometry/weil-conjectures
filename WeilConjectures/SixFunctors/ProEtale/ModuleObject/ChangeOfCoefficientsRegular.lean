/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk

/-!
# Change of coefficients and the free module of rank one

Let `a : Λ ⟶ Λ'` be a morphism of commutative condensed rings and `f : X ⟶ Y` a morphism of
schemes. The (Pull) isomorphism `Λ'_X ⊗_{Λ_X} f^* M ≅ f^* (Λ'_Y ⊗_{Λ_Y} M)` is, for the free
module `M = Λ_Y` of rank one, compatible with the identifications `f^* Λ_Y ≅ Λ_X` and
`Λ'_Y ⊗_{Λ_Y} Λ_Y ≅ Λ'_Y` (`ProEtale.CondensedRing.pullIso_hom_app_regular_comp`).

Along the way we record that the unit `R ⟶ S ⊗_R R` followed by `S ⊗_R R ≅ S` is `φ`
(`Mod.extendUnitHom_extendScalarsObjRegularIso_hom`), and that the unit of the pullback
`f^* Λ_Y ⟶ Λ_X ⊗_{f^* Λ_Y} f^* Λ_Y` followed by `f^* Λ_Y ≅ Λ_X` is `α_f`
(`ProEtale.CondensedRing.extendUnitHom_upperStarObjRegularIso_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] (φ : R ⟶ S) [IsMonHom φ]

end CategoryTheory.Mod

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj Λ] [IsCommMonObj Λ]
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

end AlgebraicGeometry.ProEtale.CondensedRing
