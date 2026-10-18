/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.TorsionReduction

/-!
# The projection formula at the integral stage `𝒪_E`

Let `E` be a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` with ring of integers `𝒪_E` and maximal ideal
`𝔪_E`. This file proves the projection formula

```
  PF_{f, K, L} : (Rf_! K) ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^* L)
```

for `K`, `L` bounded constructible, derived complete for `𝔪_E` and of finite Tor amplitude
(blueprint `sk-thm-sf-pf-adic`, with its detailed node `thm-sf-pf-adic`), following the
blueprint:

* the reduction `ρ(PF_{f, K, L})` of the projection map modulo `𝔪_E` is an isomorphism (Steps 1
  and 2 of the blueprint proof: it is the finite-level projection map `PF_{f, K₁, L₁}`);
* both sides of `PF_{f, K, L}` are derived complete (Step 3 of the blueprint proof);
* a morphism between derived complete objects whose reduction modulo `𝔪_E` is an isomorphism is
  an isomorphism (`AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal`).

## Main statements

- `AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`: the
  reconstruction step — the projection formula holds at `K` and `L` as soon as both sides of the
  projection map are derived complete and its reduction modulo `𝔪_E` is an isomorphism.
- `AlgebraicGeometry.Etale.hasProjectionFormula_of_derivedCompleteIntegral`
  (`sk-thm-sf-pf-adic`, `thm-sf-pf-adic`): the projection formula at the integral stage.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra ℚ_[l] E]
  [Algebra E (PadicAlgCl l)] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E]

variable {X Y : Scheme.{u}}

/-- **The reconstruction step of the projection formula at the integral stage.** If both sides
`Rf_! K ⊗ᴸ L` and `Rf_!(K ⊗ᴸ Lf^* L)` of the projection map are derived complete for `𝔪_E`, and
the reduction of the projection map modulo `𝔪_E` is an isomorphism, then the projection formula
holds for `f` at `K` and `L`.

This is the passage to the limit of blueprint `sk-thm-sf-pf-adic` (Step 3) and `thm-sf-pf-adic`:
the reduction modulo `𝔪_E = (ϖ)` is conservative on derived complete objects
(`AlgebraicGeometry.Etale.isIso_of_derivedComplete_of_isIso_reductionModIdeal`). -/
theorem hasProjectionFormula_of_isIso_reductionModIdeal_map (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hs : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((derivedTensor 𝐌 Y).obj ((R(f)_![𝐌]).obj K)).obj L))
    (ht : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![𝐌]).obj (((derivedTensor 𝐌 X).obj K).obj ((L((f)^*[𝐌])).obj L))))
    (hρ : IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E)).map
      (((projectionMap 𝐌 f).app K).app L))) :
    HasProjectionFormula 𝐌 f K L := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  change _root_.DerivedCategory.derivedComplete _ (PadicAlgCl.maximalIdealShrink l E) _ at hs ht
  rw [hI] at hs ht hρ
  exact isIso_of_derivedComplete_of_isIso_reductionModIdeal hϖ _ hs ht hρ

/-- Step 3 of blueprint `sk-thm-sf-pf-adic`: the source of the projection map is derived complete.

If `K` and `L` are bounded constructible, derived complete for `𝔪_E` and of finite Tor
amplitude, then `Rf_! K ⊗ᴸ L` is derived complete for `𝔪_E`. The blueprint deduces this from the
uniform-tower reconstruction (`lem-weil-pbc-reconstruction-uniform-tower`): the reductions
`Rf_! K_n ⊗ᴸ L_n` are bounded constructible of uniformly bounded amplitude. -/
theorem derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      (((derivedTensor 𝐌 Y).obj ((R(f)_![𝐌]).obj K)).obj L) :=
  sorry

/-- Step 3 of blueprint `sk-thm-sf-pf-adic`: the target of the projection map is derived
complete.

If `K` and `L` are bounded constructible, derived complete for `𝔪_E` and of finite Tor
amplitude, then `Rf_!(K ⊗ᴸ Lf^* L)` is derived complete for `𝔪_E`. As for
`AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek`, the
blueprint deduces this from the uniform-tower reconstruction
(`lem-weil-pbc-reconstruction-uniform-tower`): the reductions `Rf_!(K_n ⊗ᴸ Lf^* L_n)` are bounded
constructible of uniformly bounded amplitude. Completeness of `K ⊗ᴸ Lf^* L` alone would not
suffice: `Rf_!` does not preserve derived completeness in general (an extension by zero `j_!` of a
product of skyscraper sheaves at closed points accumulating at the boundary is not complete). -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek_derivedTensor (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![𝐌]).obj (((derivedTensor 𝐌 X).obj K).obj ((L((f)^*[𝐌])).obj L))) :=
  sorry

local instance : IsDomain (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (PadicAlgCl.shrinkRingEquiv.{w, u} l E).symm.toMulEquiv.isDomain _

local instance : IsPrincipalIdealRing (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  IsPrincipalIdealRing.of_surjective (PadicAlgCl.shrinkRingEquiv.{w, u} l E).toRingHom
    (PadicAlgCl.shrinkRingEquiv.{w, u} l E).surjective

/-- Some nonzero integer (a power of the residue characteristic) lies in `𝔪_Eⁿ`. -/
lemma exists_natCast_mem_maximalIdealShrink_pow (n : ℕ) :
    ∃ N : ℕ, N ≠ 0 ∧
      (N : Shrink.{u + 1} (PadicAlgCl.integers l E)) ∈ PadicAlgCl.maximalIdealShrink l E ^ n := by
  let k := IsLocalRing.ResidueField (PadicAlgCl.integers l E)
  have hp : ringChar k ≠ 0 := CharP.char_ne_zero_of_finite k (ringChar k)
  have hmem : ((ringChar k : ℕ) : PadicAlgCl.integers l E) ∈
      IsLocalRing.maximalIdeal (PadicAlgCl.integers l E) := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  refine ⟨ringChar k ^ n, pow_ne_zero n hp, ?_⟩
  rw [Nat.cast_pow]
  refine Ideal.pow_mem_pow ?_ n
  have := Ideal.mem_map_of_mem (PadicAlgCl.shrinkRingEquiv.{w, u} l E) hmem
  rwa [map_natCast] at this

/-- Blueprint `thm-sf-pf-field`: the compatibility with finite reduction, and Steps 1 and 2 of
`sk-thm-sf-pf-adic`.

If `K` is bounded of finite Tor amplitude and `L` is bounded constructible over `𝒪_E`, the
reduction `ρ_n(PF_{f, K, L}) = PF_{f, K, L} ⊗ᴸ (𝒪_E/𝔪_Eⁿ)_Y` of the projection map is an
isomorphism for every `n`. As in the blueprint, `ρ_n(PF_{f, K, L})` is a finite-level projection
map (`sk-prop-sf-pf-reduction`), which is an isomorphism by the argument of the finite projection
formula (`sk-thm-sf-pf-finite`): see
`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_nsmul`. Derived
completeness is not needed. -/
theorem isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible
    (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L) (n : ℕ) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E ^ n)).map
      (((projectionMap 𝐌 f).app K).app L)) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  obtain ⟨N, hN, hNJ⟩ := exists_natCast_mem_maximalIdealShrink_pow l E n
  rw [hI] at hNJ ⊢
  exact isIso_reductionModIdeal_map_projectionMap_of_nsmul hϖ n hN hNJ f K L hKc.1 hKt hLc

/-- Steps 1 and 2 of blueprint `sk-thm-sf-pf-adic`: the reduction of the projection map modulo
`𝔪_E` is an isomorphism.

If `K` and `L` are bounded constructible, derived complete for `𝔪_E` and of finite Tor
amplitude, then `ρ(PF_{f, K, L})`, the image of the projection map under the reduction
`- ⊗ᴸ (𝒪_E/𝔪_E)_Y`, is an isomorphism. In the blueprint, `ρ(PF_{f, K, L})` is identified with the
finite-level projection map `PF_{f, K₁, L₁}` by the reduction square of
`sk-prop-sf-pf-reduction`, and the latter is an isomorphism by the finite-level projection
formula `sk-thm-sf-pf-finite`; this is
`AlgebraicGeometry.Etale.isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible`
for `n = 1`. -/
theorem isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral (f : X ⟶ Y)
    [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    IsIso ((reductionModIdeal _ Y (PadicAlgCl.maximalIdealShrink l E)).map
      (((projectionMap 𝐌 f).app K).app L)) := by
  have := isIso_reductionModIdeal_pow_map_projectionMap_of_boundedConstructible l E f K L hKc hKt
    hLc 1
  rwa [pow_one] at this

/-- Blueprint `sk-thm-sf-pf-adic`: Projection formula: the derived-complete stage; and its
detailed node `thm-sf-pf-adic`: Derived-complete reconstruction over `𝒪_E`.

At the integral stage of the `ℓ`-adic formalism, where the coefficients are the ring of
integers `𝒪_E` of an extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`: if `K` and `L` are bounded
constructible, derived complete for the maximal ideal `𝔪_E` and of finite Tor amplitude, then
the projection formula holds for `f` at `K` and `L`.

The proof follows the blueprint: the reduction of the projection map modulo `𝔪_E` is an
isomorphism
(`AlgebraicGeometry.Etale.isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral`),
both its source and target are derived complete
(`AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek` and
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerShriek_derivedTensor`), and the
reduction is conservative on derived complete objects
(`AlgebraicGeometry.Etale.hasProjectionFormula_of_isIso_reductionModIdeal_map`).
Constructibility is needed for the derived completeness of the two sides: the derived tensor
product of two derived complete objects need not be derived complete. -/
theorem hasProjectionFormula_of_derivedCompleteIntegral (f : X ⟶ Y) [HasCompactification f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology 𝐌))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology 𝐌))
    (hKc : DerivedCategory.boundedConstructible 𝐌 X K)
    (hK : _root_.DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K)
    (hKt : DerivedCategory.finiteTorAmplitude 𝐌 X K)
    (hLc : DerivedCategory.boundedConstructible 𝐌 Y L)
    (hL : _root_.DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L)
    (hLt : DerivedCategory.finiteTorAmplitude 𝐌 Y L) :
    HasProjectionFormula 𝐌 f K L :=
  hasProjectionFormula_of_isIso_reductionModIdeal_map l E f K L
    (derivedCompleteIntegral_derivedTensor_rightDerivedLowerShriek l E f K L
      hKc hK hKt hLc hL hLt)
    (derivedCompleteIntegral_rightDerivedLowerShriek_derivedTensor l E f K L
      hKc hK hKt hLc hL hLt)
    (isIso_reductionModIdeal_map_projectionMap_of_derivedCompleteIntegral l E f K L
      hKc hK hKt hLc hL hLt)

end Etale

end AlgebraicGeometry
