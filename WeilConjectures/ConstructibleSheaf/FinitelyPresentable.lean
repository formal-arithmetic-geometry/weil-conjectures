/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Presentable.Finite
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Constructible sheaves are finitely presentable

On a quasi-compact quasi-separated scheme `X` and for a noetherian ring `Λ`, a constructible
sheaf of `Λ`-modules on `X_ét` is a finitely presentable object of the category of sheaves
[Stacks 09Z4].

## Main statements

- `AlgebraicGeometry.Etale.isFinitelyPresentable_of_isConstructibleSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Constructible sheaves are finitely presentable.** On a quasi-compact quasi-separated
scheme `X`, with `Λ` Noetherian, a constructible sheaf of `Λ`-modules `F` is a finitely
presentable object of the category of sheaves: `Hom(F, -)` commutes with filtered colimits
(indexed by small categories), i.e. every morphism from `F` to a filtered colimit factors
through a stage, and two such factorisations agree at a later stage.
(blueprint: `lem-weil-pbc-constructible-finitely-presented`) -/
@[stacks 09Z4]
theorem Etale.isFinitelyPresentable_of_isConstructibleSheaf [IsNoetherianRing Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    IsFinitelyPresentable.{u} F :=
  sorry

end AlgebraicGeometry
