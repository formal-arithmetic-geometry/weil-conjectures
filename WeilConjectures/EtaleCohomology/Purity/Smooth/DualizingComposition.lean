/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-!
# Additivity of the dualizing complex under composition

For composable smooth separated morphisms `g : W ⟶ X` and `f : X ⟶ Y`, the dualizing complex of
the composite is the product of the two dualizing complexes,

`ω_g ⊗^L Lg^* ω_f ⟶ Rg^! ω_f ≅ R(g ≫ f)^! Λ_Y = ω_{g ≫ f}`,

the tensor-formula map `φ` of `g` at `ω_f`, followed by the composition isomorphism of `R(-)^!` at
`Λ_Y`. This is the multiplicativity of the twist that `sk-thm-regular` divides one dualizing
complex into another with, and the composition compatibility of `sk-thm-smooth-purity`.

## Implementation notes

The composition isomorphism `AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso` is built
from the *chosen* composition isomorphism of `Rf_!`,
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso`, so the map here depends on that
choice; it is `@[no_expose]`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplexCompMap`: `ω_g ⊗^L Lg^* ω_f ⟶ ω_{g ≫ f}`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexCompMap`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {W X Y : Scheme.{u}}

/-- Blueprint `sk-prop-cohsm`: Cohomological smoothness

For `f` smooth separated of pure relative dimension `d`, the dualizing complex `ω_f` lies in
`D^b_{ctf}(X, Λ)`: by clause (a) it is a lisse rank-one sheaf of free `Λ`-modules placed in one
degree. -/
theorem constructibleFiniteTor_dualizingComplex {d : ℕ} (f : X ⟶ Y) [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasInvertibleExponent Λ X] :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (dualizingComplex (ModuleCat.{u + 1} Λ) f) :=
  sorry

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

*The composition map of dualizing complexes.* For `g : W ⟶ X` and `f : X ⟶ Y` admitting
compactifications, with `g ≫ f` admitting one too,

`ω_g ⊗^L Lg^* ω_f ⟶ Rg^! ω_f ≅ ω_{g ≫ f}`:

the tensor-formula map `AlgebraicGeometry.Etale.tensorFormulaMap` of `g` at `K = ω_f`, followed by
the inverse of the composition isomorphism `R(g ≫ f)^! Λ_Y ≅ Rg^! Rf^! Λ_Y`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekCompIso`), which depends on the chosen
composition isomorphism of `Rf_!`. It is defined whenever the projection map of `g` at
`(ω_g, ω_f)` is invertible. -/
@[no_expose]
noncomputable def dualizingComplexCompMap (g : W ⟶ X) (f : X ⟶ Y) [HasCompactification g]
    [HasCompactification f] [HasCompactification (g ≫ f)]
    [IsIso (((projectionMap (ModuleCat.{u + 1} Λ) g).app
      (dualizingComplex (ModuleCat.{u + 1} Λ) g)).app (dualizingComplex (ModuleCat.{u + 1} Λ) f))] :
    ((derivedTensor (ModuleCat.{u + 1} Λ) W).obj (dualizingComplex (ModuleCat.{u + 1} Λ) g)).obj
        ((L((g)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f)) ⟶
      dualizingComplex (ModuleCat.{u + 1} Λ) (g ≫ f) :=
  tensorFormulaMap Λ g (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≫
    ((rightDerivedUpperShriekCompIso (ModuleCat.{u + 1} Λ) g f).app (𝟙_ _)).inv

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Additivity of the dualizing complex under composition.** For composable smooth separated
`g : W ⟶ X` and `f : X ⟶ Y`, the composition map

`ω_g ⊗^L Lg^* ω_f ⟶ ω_{g ≫ f}`

is an isomorphism; with smooth purity this is the additivity `Λ(e)[2e] ⊗ Λ(d)[2d] ≅ Λ(e+d)[2(e+d)]`
of the twists. The projection map it is built from is invertible by
`AlgebraicGeometry.Etale.isIso_projectionMap_app_app`, with `ω_g` bounded constructible
(`AlgebraicGeometry.Etale.boundedConstructible_dualizingComplex`) and `ω_f ∈ D^b_{ctf}`
(`AlgebraicGeometry.Etale.constructibleFiniteTor_dualizingComplex`). -/
theorem isIso_dualizingComplexCompMap {d e : ℕ} (g : W ⟶ X) (f : X ⟶ Y) [IsSeparated g]
    [SmoothOfRelativeDimension e g] [HasCompactification g] [IsSeparated f]
    [SmoothOfRelativeDimension d f] [HasCompactification f] [HasCompactification (g ≫ f)]
    [LocallyOfFiniteType g] [HasInvertibleExponent Λ W] [HasInvertibleExponent Λ X] :
    haveI := isIso_projectionMap_app_app Λ g _ _
      (boundedConstructible_dualizingComplex Λ g (d := e))
      (constructibleFiniteTor_dualizingComplex Λ f (d := d))
    IsIso (dualizingComplexCompMap Λ g f) :=
  sorry

end Etale

end AlgebraicGeometry
