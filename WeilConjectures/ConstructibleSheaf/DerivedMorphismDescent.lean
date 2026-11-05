/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing

/-!
# Descent of morphisms in the derived category along a surjective étale morphism

Let `u : U ⟶ T` be surjective and étale, and let `Z` with projections `r₁, r₂ : Z ⟶ U` be a
fibre product `U ×_T U`. Morphisms `K ⟶ M` in `D(T_ét, Λ)` between objects which are
isomorphic to sheaves placed in degree zero descend along `u`: a morphism
`δ : Lu^* K ⟶ Lu^* M` whose two pullbacks to `Z` agree is `Lu^* γ` for some `γ : K ⟶ M`.
Morphisms between sheaves placed in one degree are morphisms of sheaves, and those glue
(`AlgebraicGeometry.Etale.exists_hom_of_upperStar`).

## Main statements

- `AlgebraicGeometry.Etale.exists_leftDerivedUpperStar_map_eq_of_isPullback`: degree zero.

The version up to a common shift is in
`WeilConjectures.ConstructibleSheaf.DerivedMorphismDescentShift`.

## Implementation notes

This file only imports `WeilConjectures.SixFunctors.Etale.Derived.HeartGluing`, which does not
see the shortcut instance `ModuleCat.isGrothendieckAbelian_of_commRing`. The derived categories
in the statement therefore carry the same `IsGrothendieckAbelian (ModuleCat Λ)` instance as the
lemmas of `HeartGluing` used in the proof. With the shortcut in scope the kernel has to
reconcile the two instance paths, which took over 100 s and 9 GB of memory.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

end AlgebraicGeometry
