/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Derived coextension of scalars commutes with the derived direct image

For a ring morphism `φ : Λ →+* Λ'`, coextension of scalars `M ↦ Hom_Λ(Λ', M)` sends étale sheaves
of `Λ`-modules to étale sheaves of `Λ'`-modules. It is right adjoint to the exact restriction of
scalars, so it preserves K-injective complexes, and it commutes with the direct image `g_*`
(both are computed objectwise). Hence its total right derived functor commutes with `Rg_*`:

`Rg_* ⋙ R coext ≅ R coext ⋙ Rg_*`.

For `Λ = 𝒪_E` and `Λ' = 𝒪_E/ϖ` the functor `R coext = RHom_{𝒪_E}(𝒪_E/ϖ, -)` is the reduction
modulo `ϖ` shifted by `-1`, read in `D(-, 𝒪_E/ϖ)`; this is a first step towards comparing
the integral and the finite stages of the projection formula (`sk-thm-sf-pf-adic`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

instance :
    PreservesLimitsOfSize.{u, u + 1} (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).rightAdjoint_preservesLimits

/- Mathlib's instance is stated for `coextendScalars.{u₁, u₂, max u₂ w}`, and unifying
`u + 1 =?= max (u + 1) ?w` gets stuck, so instance search does not find it here. -/
instance : (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ).IsRightAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).isRightAdjoint

/-- Coextension of scalars along `φ : Λ →+* Λ'`, from étale sheaves of `Λ`-modules to étale
sheaves of `Λ'`-modules. -/
noncomputable abbrev coextendScalars (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ') :=
  sheafCompose X.smallEtaleTopology (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ)

instance (X : Scheme.{u}) : (coextendScalars φ X).Additive where
  map_add {_ _ _ _} := by
    ext : 3
    rfl

instance (X : Scheme.{u}) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Coextension of scalars preserves K-injective complexes, being right adjoint to the exact
restriction of scalars. -/
instance (X : Scheme.{u}) : (coextendScalars φ X).PreservesKInjectiveComplexes :=
  (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).preservesKInjectiveComplexes

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- Coextension of scalars commutes with the direct image, both being computed objectwise. -/
noncomputable def lowerStarCompCoextendScalarsIso :
    (g)_*[ModuleCat.{u + 1} Λ] ⋙ coextendScalars φ Y ≅
      coextendScalars φ Z ⋙ (g)_*[ModuleCat.{u + 1} Λ'] :=
  Iso.refl _

/-- **Derived coextension of scalars commutes with `Rg_*`.** -/
noncomputable def rightDerivedLowerStarCompCoextendScalarsIso :
    ((g)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctor ⋙
        (coextendScalars φ Y).rightDerivedFunctor ≅
      (coextendScalars φ Z).rightDerivedFunctor ⋙
        ((g)_*[ModuleCat.{u + 1} Λ']).rightDerivedFunctor :=
  Functor.rightDerivedFunctorCompIso' _ _ (lowerStarCompCoextendScalarsIso φ g) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (Iso.refl _)).symm

end Etale

end AlgebraicGeometry
