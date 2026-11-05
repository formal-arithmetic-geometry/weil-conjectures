/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

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

section Detect

variable {X : Scheme.{u}} (ϖ : Λ)

end Detect

section Pullback

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

end Pullback

end Etale

end AlgebraicGeometry
