/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleDescent
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-!
# Complexes étale-locally concentrated in one degree

Let `u : U ⟶ T` be surjective and étale and let `K ∈ D(T_ét, Λ)`. If `Lu^* K` is a finite
locally constant sheaf placed in degree `r`, then so is `K`: the cohomology sheaves of `K` vanish
outside degree `r` (`AlgebraicGeometry.Etale.isZero_homology_of_leftDerivedUpperStar_iso`) and
`H^r(K)` is finite locally constant
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso`).
Together with `DerivedCategory.nonempty_iso_singleFunctor_obj_homologyFunctor_obj` this is the
blueprint lemma `lem-pur-concentrated-complex-shift`.

## Main statements

- `AlgebraicGeometry.Etale.isZero_homology_of_leftDerivedUpperStar_iso`,
  `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_homology_of_leftDerivedUpperStar_iso`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {U T : Scheme.{u}} (u : U ⟶ T) [Etale u] [Surjective u]
  {K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {r : ℤ}
  {L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

end Etale

end AlgebraicGeometry
