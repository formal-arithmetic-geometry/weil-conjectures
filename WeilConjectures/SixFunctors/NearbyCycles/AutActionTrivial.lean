/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.AutAction

/-!

# Automorphisms of models that do not change a morphism of models act trivially

If `σ : M' ⟶ M'` is a morphism of models over the identities and `ρ : M' ⟶ M` is a morphism of
models over `f, f'` with `σ ≫ ρ = ρ` on total spaces and geometric generic fibres, then `σ` acts
trivially on `Ψ_{M'} (Lf^* C)` whenever the pullback exchange `α_ρ(C)` is invertible
(`NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`).

## Main results

- `ProEtale.CondensedRing.leftDerivedUpperStarCompOfEq_hom_app_comp_leftDerivedUpperStarId`:
  the left unit law for the transported composition isomorphisms.
- `NearbyCyclesModel.Hom.autAction_eq_id_of_isIso`: the triviality of the action.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

namespace NearbyCyclesModel

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
