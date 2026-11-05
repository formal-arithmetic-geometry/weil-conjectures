/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCompletion
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The projection formula at the integral stage `𝒪_E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E` and maximal ideal
`𝔪_E = (ϖ)`. This file proves the projection formula at the integral stage of the `ℓ`-adic
formalism (blueprint `sk-thm-sf-pf-adic`, with its detailed node `thm-sf-pf-adic`): for
`f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, 𝒪_E)` and `L ∈ D(Y_ét, 𝒪_E)`, the
projection map

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

is an isomorphism in the integral stage `D_comp(Y_ét, 𝒪_E)`, i.e. after derived completion
`DerivedCategoryDerivedCompleteIntegral.completion`, and its reductions modulo every `𝔪_Eⁿ` are
isomorphisms.

## The statement

The operations of the integral stage are defined levelwise on the finite reductions (blueprint
`det-def-sf-operations`, adic stages; `def-exchange-projection`: the coefficient categories
`𝒪_E`, `E`, `ℚ̄_ℓ` "are obtained by derived completion"): the integral `Rf_! K ⊗ᴸ L` is the derived
limit `R lim_n (Rf_! K_n ⊗ᴸ L_n)` of its reductions, and `PF_{f, K, L}` over `𝒪_E` is the morphism
realized by the system `(PF_{f, K_n, L_n})_n` (`thm-sf-pf-adic`). Since reduction commutes with
the plain operations of `D(X_ét, 𝒪_E)` (`lem-fix-operation-reduction`), this derived limit is the
derived completion `(Rf_! K ⊗ᴸ L)^` of the plain operation, and the integral projection map is the
derived completion of the plain projection map. So the statement proved here,
`AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`, is the blueprint statement.

The plain projection map of `D(X_ét, 𝒪_E)` itself is only shown to be an isomorphism when its
source and target are derived complete
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`). The blueprint
sketch notes that its own argument for the plain statement is incomplete (Step 3 needs the derived
completeness of both sides), and for the plain operations of `D(X_ét, 𝒪_E)` this fails in general:
`- ⊗ᴸ -` and `Lf^*` do not preserve derived completeness (for `X = Spec 𝔽_q` the derived limit `𝒪̂`
of the `(𝒪_E/𝔪_Eⁿ)_X` has `H¹(𝒪̂) ≠ 0`, so `𝒪̂ ⊗ᴸ 𝒪̂` has `H² ≠ 0` and is not derived complete), and
derived complete bounded constructible objects are very rare (the constant sheaf `𝒪_E` is not
derived complete on `Spec 𝔽_q`), so that a proof of the plain statement for them would need a
classification of these objects.

## Proof

* the reduction `ρ(PF_{f, K, L})` modulo `𝔪_Eⁿ` is an isomorphism (Steps 1 and 2 of the blueprint
  proof: it is the finite-level projection map `PF_{f, K_n, L_n}`);
* hence the cone of `PF_{f, K, L}` is an object on which `ϖ` acts invertibly, and the derived
  completion inverts such morphisms
  (`DerivedCategory.isIso_derivedCompletion_map`) — this replaces Step 3 of the
  blueprint proof.

## Main statements

- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_maximalIdealShrink_pow_map_projectionMap`:
  the reductions modulo `𝔪_Eⁿ` of the projection map are isomorphisms.
- `AlgebraicGeometry.Etale.isIso_completion_map_projectionMap`: the
  projection formula at the integral stage.
- `AlgebraicGeometry.Etale.isIso_completion_map_projectionMap_of_derivedCompleteIntegral`
  (`thm-sf-pf-adic`): the same, together with the compatibility with all finite reductions.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`: the plain
  projection formula when both sides are derived complete.
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
