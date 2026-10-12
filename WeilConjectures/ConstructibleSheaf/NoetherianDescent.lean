/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Descent of constructible sheaves to a Noetherian scheme

A constructible sheaf of `Λ`-modules on a quasi-compact quasi-separated scheme, for a noetherian
ring `Λ`, is the pullback of a constructible sheaf on a Noetherian scheme: write the scheme as a
cofiltered limit of Noetherian schemes with affine transition maps [Stacks 01ZA] and descend the
finitely many étale objects, sections and relations presenting the sheaf to one stage.

## Main statements

- `AlgebraicGeometry.Etale.exists_isNoetherian_upperStar_iso`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **Descent of a constructible sheaf to a Noetherian scheme.** A constructible sheaf of
`Λ`-modules on a quasi-compact quasi-separated scheme `U`, for `Λ` noetherian, is the pullback
of a constructible sheaf on a Noetherian scheme `U'` along some morphism `U ⟶ U'`: its strata
are constructible and its finitely generated stalks finitely presented, so write `U` as a
cofiltered limit of schemes of finite type over `ℤ` with affine transition maps [Stacks 01ZA] and
descend the finitely many étale objects, sections and relations presenting `C` to one stage.
This is Step 2 of `lem-weil-pbc-constructible-finite-pushforward-approximation`. -/
theorem Etale.exists_isNoetherian_upperStar_iso [IsNoetherianRing Λ] {U : Scheme.{u}}
    [CompactSpace U]
    [QuasiSeparatedSpace U] (C : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf C] :
    ∃ (U' : Scheme.{u}) (ν : U ⟶ U') (C' : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsNoetherian U' ∧ IsConstructibleSheaf C' ∧ Nonempty (((ν)^*[_]).obj C' ≅ C) :=
  sorry

end AlgebraicGeometry
