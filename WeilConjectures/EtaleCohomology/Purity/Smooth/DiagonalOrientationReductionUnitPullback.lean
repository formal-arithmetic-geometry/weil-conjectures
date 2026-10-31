/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnit

/-!
# The commutation of the reduction of coefficients with the derived pullback preserves the units

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel, `Ψ` the
derived extension of scalars and `e : U ⟶ X` a morphism of schemes. The commutation
`Le^* ⋙ Ψ_U ⟶ Ψ_X ⋙ Le^*`, through the counits
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackOfCounit`), is compatible with the unit
comparisons of the monoidal functors `Ψ` and of the oplax monoidal derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackOfCounit_app_unit_comp_η`): through the
counits it is the underived commutation, which preserves the units.
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

variable (X) in
/-- The unit comparison of the derived extension of scalars, through the unit comparisons of the
localization functors and the counit at the unit (`Functor.leftDerivedFunctorMonoidal_η`). -/
lemma leftDerivedFunctor_extendScalars_η_comp_ε :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    η (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor ≫ ε DerivedCategory.Qh =
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor.map (ε DerivedCategory.Qh) ≫
        (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app (𝟙_ _) ≫
          DerivedCategory.Qh.map
            (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  Functor.leftDerivedFunctorMonoidal_η _

/-- `AlgebraicGeometry.Etale.derivedExtendScalarsPullbackOfCounit_app_Qh` at the unit, in terms
of the counits of the left derived functors. -/
@[reassoc]
lemma derivedExtendScalarsPullbackOfCounit_app_Qh_unit :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha U
    (derivedExtendScalarsPullbackOfCounit hρ ha e).app (DerivedCategory.Qh.obj (𝟙_ _)) ≫
        L((e)^*[ModuleCat.{u + 1} Λ']).map
          ((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit.app (𝟙_ _)) ≫
        ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
          (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj (𝟙_ _)) =
      (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctor.map
          (((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit.app (𝟙_ _)) ≫
        (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.app
          ((((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)).obj (𝟙_ _)) ≫
        DerivedCategory.Qh.map ((extendScalarsUpperStarHomotopyIso ρ e).inv.app (𝟙_ _)) := by
  have h := derivedExtendScalarsPullbackOfCounit_app_Qh hρ ha e (𝟙_ _)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at h
  exact h

/-- Blueprint `det-sp-purity-coefficient-change` (the unit compatibility of the commutation of `Ψ`
with `Le^*`).

**The commutation of `Ψ` with the derived pullback preserves the units**:
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
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have := preservesKFlatQuasiIso_extendScalars hρ ha U
  let := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
  let := (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
  let := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) e
  let := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ') e
  have := DerivedCategory.isIso_ε_Qh (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  have hΨX := leftDerivedFunctor_extendScalars_η_comp_ε hρ ha X
  have hΨU := leftDerivedFunctor_extendScalars_η_comp_ε hρ ha U
  have he := leftDerivedUpperStarOplaxMonoidal_η_comp_ε Λ e
  have he' := leftDerivedUpperStarOplaxMonoidal_η_comp_ε Λ' e
  have hn₁ := ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.naturality
    (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))
  have hn₂ := (Sheaf.extendScalars U.smallEtaleTopology ρ).leftDerivedFunctorCounit.naturality
    (η (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ)))
  have hn₃ := (derivedExtendScalarsPullbackOfCounit hρ ha e).naturality
    (ε (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
  have hc := derivedExtendScalarsPullbackOfCounit_app_Qh_unit hρ ha e
  have hH := extendScalarsUpperStarHomotopyIso_inv_app_unit_comp_η ρ e
  simp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂ hn₃
  have hH' := congrArg DerivedCategory.Qh.map hH
  simp only [Functor.map_comp] at hn₁ hn₂ hn₃ hH'
  dsimp only [derivedExtendScalars] at hn₃
  rw [← cancel_mono (ε DerivedCategory.Qh), Category.assoc, Category.assoc, he', Category.assoc,
    hΨU, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hΨX, he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn₃, reassoc_of% hn₁, reassoc_of% hc, hH', reassoc_of% hn₂]

end AlgebraicGeometry.Etale
