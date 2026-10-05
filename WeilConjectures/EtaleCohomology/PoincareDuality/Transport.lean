/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Finiteness
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing

/-!
# Transport through the coefficient stages

The blueprint builds the Poincaré pairing at the finite stages `A_{E,n} = 𝒪_E/ϖ^n` and
carries it to `𝒪_E`, `E` and `ℚ̄_ℓ` by the uniform-tower reconstruction and by descent along
the common-stage construction. In this repository a coefficient stage is a ring `Λ` with the
category `ModuleCat Λ`, the finite reduction along an ideal `J` is the endofunctor
`AlgebraicGeometry.Etale.reductionModIdeal` (`K ↦ K ⊗ᴸ (Λ/J)_X`) of `D(X_ét, Λ)`, and the
`𝒪_E` stage is the derived-complete subcategory
`DerivedCategory.derivedCompleteIntegral`. Following
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`, this file states only the
genuinely new content of `sk-thm-transport` that the API can express.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`: `Ra_*`
  commutes with finite reduction; together with
  `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` for `Ra_!`
  this identifies the two sides of the reduced pairing with the reductions of the two sides of
  `β_K`.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_reductionModIdeal`: the
  derived Poincaré pairing of the reduction `K ⊗ᴸ (Λ/J)_X` is perfect whenever that of `K` is.
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_coefficientDual`: at `Λ = 𝒪_E` the dual
  `K^∨` of a derived-complete `K` is derived complete. With
  `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek` and
  `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar` (`sk-lem-finite`)
  this places every object of `β_K` in the adic category `D_comp(−, 𝒪_E)`, so that the
  pairing and its perfectness at `𝒪_E` are the statements of
  `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` read at `Λ = 𝒪_E`.

## Not stated

- *Change of coefficient ring.* The reduction `A_{E,n} → A_{E,m}` as a change of the ring of
  coefficients, and the comparison of the pairing over `Λ/J` with the reduction of the pairing
  over `Λ`, need a restriction-of-scalars functor between `D(X_ét, Λ)` and
  `D(X_ét, Λ/J)`, which the repository does not have; `reductionModIdeal` stays inside
  `D(X_ét, Λ)`.
- *The `E` and `ℚ̄_ℓ` stages.* `AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`
  carries no `Rf_!`, and the colimit over finite `E/ℚ_ℓ` does not exist in the repository.
- *The trace isomorphism and the Frobenius statements.* They are built from the pairing and
  the smooth trace, and transport with them; the Frobenius statements belong to
  `sk-thm-frobenius`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section FiniteReduction

variable (Λ : Type (u + 1)) [CommRing Λ]
  {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ} (S : PoincareDualitySetting k₀ d)
  (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`RΓ` commutes with finite reduction.** For an ideal `J` of the finite coefficient ring `Λ`
and `K ∈ D^b_{ctf}(X, Λ)`,

`(Ra_* K) ⊗ᴸ (Λ/J)_s ≅ Ra_*(K ⊗ᴸ (Λ/J)_X)`.

This is the ordinary counterpart of
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek`; together
they identify the two factors of the reduced pairing with the reductions of the two factors
of `β_K`. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedLowerStar [Finite Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))] (J : Ideal Λ)
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K) :
    Nonempty ((reductionModIdeal Λ (Spec (CommRingCat.of k)) J).obj
        ((R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R((S.structureMorphism k)_*[ModuleCat.{u + 1} Λ])).obj
        ((reductionModIdeal Λ (S.geometricFiber k) J).obj K)) :=
  sorry

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The duality is compatible with finite reduction.** For an ideal `J` of the finite
coefficient ring `Λ` and `K ∈ D^b_{ctf}(X, Λ)`: if the derived Poincaré pairing `β_K` is
perfect, then so is the pairing `β_{K ⊗ᴸ (Λ/J)}` of the reduction of `K`. The reduction of a
perfect complex need not be perfect over `Λ`, so this is not an instance of the duality for
`K ⊗ᴸ (Λ/J)` itself: it is the passage from the integral level to the finite levels. -/
theorem isPerfectPairing_poincarePairing_reductionModIdeal [Finite Λ] [HasTateTwist Λ]
    [HasInvertibleExponent Λ (Spec (CommRingCat.of k))]
    [HasCompactification (S.structureMorphism k)]
    (γ : (twistShift Λ (S.geometricFiber k) d).obj (constantComplex Λ (S.geometricFiber k)) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (S.structureMorphism k))
    (J : Ideal Λ)
    (K : _root_.DerivedCategory (Sheaf (S.geometricFiber k).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ (S.geometricFiber k) K)
    (hβ : DerivedCategory.IsPerfectPairing (poincarePairing Λ (S.structureMorphism k) d γ K)) :
    DerivedCategory.IsPerfectPairing (poincarePairing Λ (S.structureMorphism k) d γ
      ((reductionModIdeal Λ (S.geometricFiber k) J).obj K)) :=
  sorry

end FiniteReduction

section IntegralStage

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E]

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The dual at the integral stage.** At `Λ = 𝒪_E`, the coefficient dual `K^∨ = RHom(K, Λ_X)`
of a derived-complete object of `D(X_ét, 𝒪_E)` is derived complete. Together with
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek` and
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar` this places both
factors of `β_K` in the adic category `D_comp(s, 𝒪_E)`. -/
theorem derivedCompleteIntegral_coefficientDual {X : Scheme.{u}}
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((DerivedCategory.coefficientDual
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X).obj (op K)) :=
  sorry

end IntegralStage

end Etale

end AlgebraicGeometry
