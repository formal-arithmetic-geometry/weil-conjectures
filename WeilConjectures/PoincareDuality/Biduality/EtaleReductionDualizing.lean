/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekIso

/-!
# The reduction of the integral dualizing complex

Write `red_X : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the reduction modulo `ℓⁿ` read on the small
étale site (`ProEtale.CondensedRing.etaleReduction`). This file proves that `red_X` carries the
integral dualizing complex `ω_{X, 𝒪_E} = Ra_X^! 𝒪_E` to the étale dualizing complex
`ω_X = Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint `det-pd-biduality-coefficients`, proof of (ii), from the
coefficient comparison for `f^!` of blueprint `det-prop-scalar-six-exceptional`).

The structure morphism `a_X` factors through a compactification as an open immersion `j`
followed by a proper `p`; the reduction commutes with `Rp^!` (`exists_etaleReductionLowerShriekIso`)
and with `Rj^! = j^*` (`nonempty_etaleReductionUpperStarIso`).

## Main definitions

- `ProEtale.CondensedRing.etaleReductionDualizingComplexIso`:
  `red_X ω_{X, 𝒪_E} ≅ ω_X`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- **The reduction of the integral dualizing complex is the étale dualizing complex**:
`red_X (Ra_X^! 𝒪_E) ≅ Ra_X^! (𝒪_E ⧸ ℓⁿ)` (blueprint `det-prop-scalar-six-exceptional` for
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site, at the unit). -/
noncomputable def etaleReductionDualizingComplexIso :
    (etaleReduction ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E X) ≅
      Etale.dualizingComplex (integersModPowCoeff.{u} ℓ E n) X.hom :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
