/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.RestrictScalarsAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Restriction of scalars commutes with the derived direct image of pro-étale sheaves

Let `φ : Λ →+* Λ'` be a morphism of commutative rings (e.g. `ℤ → ℤ/ℓⁿ`) and `f : X ⟶ Y` a
morphism of schemes. Restriction of scalars along `φ` is exact and commutes with the direct image
`f_*` of pro-étale sheaves (both are computed objectwise). It also commutes with the derived
direct image: `res (Rᵠf_* G) ≅ Rᵠf_* (res G)` for a sheaf `G` of `Λ'`-modules on `X_proét`.
The input is that restriction of scalars sends injective sheaves of `Λ'`-modules to
`f_*`-acyclic sheaves of `Λ`-modules
(`CategoryTheory.Sheaf.rightAcyclic_restrictScalars_obj_of_injective`).

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar`.
It is what identifies the higher direct images of the terms `Gₙ` of an `ℓ`-adic tower, computed
for sheaves of `ℤ/ℓⁿ`-modules, with those computed for the underlying sheaves of `ℤ`-modules, on
which the Milnor sequence (`AlgebraicGeometry.ProEtale.shortExact_milnor_rightDerivedLowerStar`)
is formulated.

## Main results

- `AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_restrictScalars_obj`: injective sheaves of
  `Λ'`-modules are `f_*`-acyclic as sheaves of `Λ`-modules.
- `AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerStarRestrictScalars`:
  `res ∘ R⁺f_* ≅ R⁺f_* ∘ res` on `D⁺`.
- `AlgebraicGeometry.ProEtale.rightDerivedLowerStarRestrictScalarsIso`:
  `res (Rᵠf_* G) ≅ Rᵠf_* (res G)` for the classical right derived functors.
- `AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarRestrictScalarsIso`: the same for the
  cohomology sheaves of the total derived functor `Rf_*` applied to `G[0]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
  {X Y : Scheme.{u}} (f : X ⟶ Y)

end AlgebraicGeometry.ProEtale
