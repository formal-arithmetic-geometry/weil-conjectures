/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# The projection map and reduction of the coefficient ring

Let `Λ` be a commutative ring and `ϖ` a nonzerodivisor of `Λ`, the intended case being
`Λ = 𝒪_E` with a uniformizer `ϖ`, so that `Λ ⧸ (ϖ)ⁿ = A_{E,n}`. Reduction of coefficients
`K ↦ K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`, from `D(X_ét, Λ)` to `D(X_ét, Λ ⧸ (ϖ)ⁿ)`, commutes with `Lf^*`, with
`⊗ᴸ` and with `Rf_!`, compatibly with the units and counits out of which the projection map is
built. Read through restriction of scalars, this says that the reduction modulo `(ϖ)ⁿ` of the
projection map `PF_{f, K, L}` over `Λ` is, up to isomorphism of arrows, the projection map
`PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ` of the reductions.

## Main statements

- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap`
  (`lem-fix-operation-reduction`): the reduction of `PF_{f, K, L}` modulo `(ϖ)ⁿ` is isomorphic,
  as an arrow, to the restriction of scalars of `PF_{f, K_n, L_n}`.
- `AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_finite`: if
  `Λ ⧸ (ϖ)ⁿ` is finite, the reduction of `PF_{f, K, L}` modulo `(ϖ)ⁿ` is an isomorphism for all
  `K` and `L`, by the finite-level projection formula
  (`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`).

## Implementation notes

As in `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`, the reduction
`K_n ∈ D(X_ét, Λ ⧸ (ϖ)ⁿ)` is characterised by its universal property
(`AlgebraicGeometry.Etale.IsDerivedBaseChange`), and the reduction modulo `(ϖ)ⁿ` of a morphism
of `D(Y_ét, Λ)` is its image under `AlgebraicGeometry.Etale.reductionModIdeal`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ ⧸ (ϖ)ⁿ` (for `Λ = 𝒪_E`, the reduction `𝒪_E → A_{E,n}`) with
the projection transformation.

For a nonzerodivisor `ϖ` of `Λ`, `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, there are reductions `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ` and `L_n = L ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`
(derived base changes, `AlgebraicGeometry.Etale.IsDerivedBaseChange`) such that the reduction
`ρ(PF_{f, K, L})` of the projection map, its image under `- ⊗ᴸ (Λ ⧸ (ϖ)ⁿ)_Y`, is isomorphic as an
arrow to the restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ`.

The blueprint node states that the reduction `𝒪_E → A_{E,n}` commutes with `Lf^*`, `⊗ᴸ` and the
compact-support direct image, the comparisons preserving the associativity maps, units and counits
used to construct the projection transformation; the displayed arrow isomorphism is that
compatibility for the projection map. It is the reduction square that Step 1 of
`sk-thm-sf-pf-adic` cites from `sk-prop-sf-pf-reduction`. -/
theorem exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (L : 𝐃(Y, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X).obj Kn)
      (Ln : 𝐃(Y, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).obj Ln),
      IsDerivedBaseChange η ∧ IsDerivedBaseChange η' ∧
        Nonempty (Arrow.mk ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
            (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L)) ≅
          Arrow.mk ((derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).map
            (((projectionMap (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) f).app Kn).app Ln))) :=
  sorry

/-- **The reduction of the projection map at a finite quotient.** For a nonzerodivisor `ϖ` of
`Λ` with `Λ ⧸ (ϖ)ⁿ` finite, `f : X ⟶ Y` admitting a compactification, and arbitrary
`K ∈ D(X_ét, Λ)` and `L ∈ D(Y_ét, Λ)`, the reduction modulo `(ϖ)ⁿ` of the projection map
`PF_{f, K, L}` is an isomorphism: it is the restriction of scalars of the projection map
`PF_{f, K_n, L_n}` over the finite ring `Λ ⧸ (ϖ)ⁿ`
(`AlgebraicGeometry.Etale.exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap`),
which is an isomorphism by the finite-level projection formula
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_finite`). -/
theorem isIso_reductionModIdeal_map_projectionMap_of_finite (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) [Finite (Λ ⧸ Ideal.span {ϖ} ^ n)] (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (L : 𝐃(Y, Λ)) :
    IsIso ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
      (((projectionMap (ModuleCat.{u + 1} Λ) f).app K).app L)) := by
  obtain ⟨Kn, -, Ln, -, -, -, ⟨e⟩⟩ :=
    exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap hϖ n f K L
  have : IsIso (((projectionMap (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) f).app Kn).app Ln) :=
    hasProjectionFormula_of_finite _ f Kn Ln
  exact (isIso_iff_of_arrow_mk_iso e).2 inferInstance

end Etale

end AlgebraicGeometry
