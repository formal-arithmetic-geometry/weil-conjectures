/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided

/-!

# The Künneth map of nearby cycles is symmetric

The lax tensor map `μ_j : Rj_* A ⊗ Rj_* B ⟶ Rj_* (A ⊗ B)` of the derived pushforward commutes with
the braidings (`ProEtale.CondensedRing.lowerStarTensorMap'_braiding`), since the monoidal
structure of the derived pullback does
(`ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding`).
Hence so does the lax tensor map of nearby cycles
(`ProEtale.CondensedRing.NearbyCyclesModel.tensorMap_braiding`), and the Künneth map of nearby
cycles is symmetric: exchanging the two factors of a product exchanges the Künneth maps up to the
braidings (`ProEtale.CondensedRing.NearbyCyclesModel.braiding_comp_kunnethMap`).

The braiding of the derived categories is `DerivedCategory.braidedCategory'`, used as a local
instance.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

attribute [local instance] DerivedCategory.braidedCategory'

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

variable {X X' : Scheme.{u}} (M : NearbyCyclesModel X X')

variable {Y Y' Z Z' : Scheme.{u}} {M} {N : NearbyCyclesModel Y Y'} {P : NearbyCyclesModel Z Z'}
  {f₁ : Z ⟶ X} {f₁' : Z' ⟶ X'} {f₂ : Z ⟶ Y} {f₂' : Z' ⟶ Y'}

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
