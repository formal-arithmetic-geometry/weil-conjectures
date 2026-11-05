/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral

/-!
# The projection formula at the rational stage `E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. The rational
stage `D_comp(Y_ét, E)` of the `ℓ`-adic formalism is the rationalization
`DerivedCategoryDerivedCompleteRational` of the integral stage `D_comp(Y_ét, 𝒪_E)`, and the
operations `Rf_!`, `⊗ᴸ` and `Lf^*` on rationalized objects are induced by the integral ones, which
are the derived completions of the plain operations of `D(Y_ét, 𝒪_E)` (see
`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral`). So the projection map
`PF_{f, K, L}` over `E`, for `K` and `L` obtained by rationalization from `𝒪_E`-objects, is the
image of the integral projection map, the derived completion of the plain projection map, under
the localization functor `DerivedCategoryDerivedCompleteRational.fromIntegral`. This file proves
that it is an isomorphism (blueprint `thm-sf-pf-field`, rational stage), following the blueprint:
the integral projection map is an isomorphism (`sk-thm-sf-pf-adic`,
`AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`), and a functor carries
isomorphisms to isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.isIso_fromIntegral_map_projectionMap` (`thm-sf-pf-field`): the
  projection formula over `E` for rationalizations of `𝒪_E`-objects.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap` (`thm-sf-pf-field`):
  the reductions modulo `𝔪_Eⁿ` of the integral representative are isomorphisms.
- `AlgebraicGeometry.Etale.hasProjectionFormula_field`: both together.

## Implementation notes

The blueprint states these for rationalizations of bounded constructible, derived complete
`𝒪_E`-objects of finite Tor amplitude; the statements here hold for all `𝒪_E`-objects.

The stage `ℚ̄_ℓ` of the blueprint concerns objects represented at a finite stage `E'/ℚ_ℓ`; for
those the projection map is the scalar extension of the projection map over `E'`, an isomorphism
by the statement here for `E'`, `E` being an arbitrary finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`.
The `2`-colimit category over the finite stages is not built in the étale model, and the
compatibility of the projection map with the scalar extension functors `E ⟶ E'` is not stated:
those functors (extension of scalars `𝒪_E ⟶ 𝒪_{E'}` on étale derived categories, and their
commutation with `Rf_!`, `⊗ᴸ` and `Lf^*`) are not constructed yet.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. The ring structure is written
as the one underlying the commutative ring structure, as in the statements of the lemmas for
general commutative coefficient rings that are applied to it. -/
local notation "𝐌" =>
  @ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)) CommRing.toRing

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

end Etale

end AlgebraicGeometry
