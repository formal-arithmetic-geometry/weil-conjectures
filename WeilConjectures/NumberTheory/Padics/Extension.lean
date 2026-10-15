/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Valued.NormedValued

/-!

# Extensions of `ℚ_ℓ` inside `ℚ̄_ℓ` and their rings of integers

Let `E` be a field with an embedding `E → ℚ̄_ℓ = PadicAlgCl l`. This file restricts the
`ℓ`-adic norm and valuation of `ℚ̄_ℓ` to `E`, defines the ring of integers `𝒪_E` as the
valuation subring of the restricted valuation, and shows that `𝒪_E` is `𝔪_E`-adically
complete when `E` is a finite extension of `ℚ_ℓ`.

The valuation and topology of `E` are not separate data but are restricted from `ℚ̄_ℓ` along
the embedding. These structures are definitions rather than instances, since `ℓ` cannot be
recovered from `E`. The structure is phrased with `Valued`, pending the move of this part of
mathlib to `ValuativeRel`.

The ring of integers only uses the embedding `E → ℚ̄_ℓ`. The `ℚ_ℓ`-algebra structure, the
scalar tower and finiteness `[FiniteDimensional ℚ_[l] E]` are used for the completeness of
`𝒪_E` (`PadicAlgCl.isAdicComplete_integers`): through them the restricted valuation extends
the `ℓ`-adic one, and `E` becomes a nonarchimedean local field.

## Main definitions

- `PadicAlgCl.normedFieldOfAlgebra`, `PadicAlgCl.valuationOfAlgebra` and
  `PadicAlgCl.valuedOfAlgebra` : the norm, valuation and valued field structure of `E`,
  restricted from `ℚ̄_ℓ`.
- `PadicAlgCl.integers` : the ring of integers `𝒪_E`.
- `PadicAlgCl.shrinkRingEquiv` and `PadicAlgCl.maximalIdealShrink` : the identification of
  `𝒪_E` with its copy `Shrink.{u + 1} 𝒪_E`, and the maximal ideal `𝔪_E` read in that copy.

## Main results

- `PadicAlgCl.isAdicComplete_integers` and `PadicAlgCl.isAdicComplete_maximalIdealShrink` :
  if `E` is finite over `ℚ_ℓ`, then `𝒪_E` and its copy `Shrink 𝒪_E` are `𝔪_E`-adically
  complete.

-/

@[expose] public section

universe w u

open NNReal

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]

/-- The normed field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
the `ℓ`-adic norm of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. Its topology is
the subspace topology of `E` in `PadicAlgCl l`. -/
@[reducible]
noncomputable def normedFieldOfAlgebra : NormedField E :=
  NormedField.induced E (PadicAlgCl l) (algebraMap E (PadicAlgCl l))
    (algebraMap E (PadicAlgCl l)).injective

/-- The `ℓ`-adic valuation on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from the
valuation of `PadicAlgCl l` along the embedding `E → PadicAlgCl l`. -/
noncomputable def valuationOfAlgebra : Valuation E ℝ≥0 :=
  (Valued.v : Valuation (PadicAlgCl l) ℝ≥0).comap (algebraMap E (PadicAlgCl l))

variable {l E} in
lemma valuationOfAlgebra_apply (x : E) :
    valuationOfAlgebra l E x = ‖algebraMap E (PadicAlgCl l) x‖₊ := rfl

lemma isUltrametricDist_ofAlgebra :
    letI := normedFieldOfAlgebra l E
    IsUltrametricDist E := by
  let := normedFieldOfAlgebra l E
  exact IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun x y ↦ by
    have := PadicAlgCl.isNonarchimedean l (algebraMap E (PadicAlgCl l) x)
      (algebraMap E (PadicAlgCl l) y)
    rwa [← map_add] at this

/-- The valued field structure on a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`, restricted from
`PadicAlgCl l`: its valuation is `PadicAlgCl.valuationOfAlgebra` and its uniformity that of
`PadicAlgCl.normedFieldOfAlgebra`.

It is not an instance, since `ℓ` cannot be recovered from `E`. -/
@[reducible]
noncomputable def valuedOfAlgebra : Valued E ℝ≥0 :=
  letI := normedFieldOfAlgebra l E
  haveI := isUltrametricDist_ofAlgebra l E
  NormedField.toValued

lemma valuedOfAlgebra_v : (valuedOfAlgebra l E).v = valuationOfAlgebra l E := rfl

/-- The ring of integers `𝒪_E` of a subfield `E` of `ℚ̄_ℓ = PadicAlgCl l`: the valuation
subring of the valuation `PadicAlgCl.valuationOfAlgebra` restricted from `PadicAlgCl l`. -/
noncomputable def integers : ValuationSubring E :=
  (valuationOfAlgebra l E).valuationSubring

lemma mem_integers_iff (x : E) :
    x ∈ integers l E ↔ ‖algebraMap E (PadicAlgCl l) x‖₊ ≤ 1 := Iff.rfl

/-- The identification of the ring of integers `𝒪_E` with its copy `Shrink 𝒪_E` in the
universe `u + 1`, where the coefficient ring of a sheaf on a `u`-site has to live. -/
noncomputable def shrinkRingEquiv [Small.{u + 1} E] :
    integers l E ≃+* Shrink.{u + 1} (integers l E) :=
  (Shrink.ringEquiv (integers l E)).symm

/-- The maximal ideal `𝔪_E` of the ring of integers `𝒪_E`, read inside the universe `u + 1`
copy `Shrink 𝒪_E` along `PadicAlgCl.shrinkRingEquiv`. This is the ideal with respect to which
the objects of `D(J, 𝒪_E)` are asked to be derived complete. -/
noncomputable def maximalIdealShrink [Small.{u + 1} E] : Ideal (Shrink.{u + 1} (integers l E)) :=
  (IsLocalRing.maximalIdeal (integers l E)).map (shrinkRingEquiv l E)

section Complete

variable [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]

lemma valuationOfAlgebra_algebraMap (x : ℚ_[l]) :
    valuationOfAlgebra l E (algebraMap ℚ_[l] E x) = ‖x‖₊ := by
  rw [valuationOfAlgebra_apply, ← IsScalarTower.algebraMap_apply]
  exact NNReal.eq (PadicAlgCl.norm_extends l x)

open ValuativeRel in
/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, its ring of integers is
`𝔪_E`-adically complete.

The proof equips `E` with the valuative relation and the topology restricted from
`PadicAlgCl l`, checks that this makes `E` a nonarchimedean local field (it is locally
compact, being a finite-dimensional normed space over `ℚ_ℓ`), and transports mathlib's
`IsAdicComplete 𝓂[E] 𝒪[E]` to `PadicAlgCl.integers l E`. -/
instance isAdicComplete_integers [FiniteDimensional ℚ_[l] E] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integers l E)) (integers l E) := by
  let w := valuationOfAlgebra l E
  let := normedFieldOfAlgebra l E
  have := isUltrametricDist_ofAlgebra l E
  let : ValuativeRel E := .ofValuation w
  have : w.Compatible := .ofValuation w
  let : NormedSpace ℚ_[l] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl l) (c • x)‖ ≤ ‖c‖ * ‖algebraMap E (PadicAlgCl l) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have : ProperSpace E := FiniteDimensional.proper ℚ_[l] E
  have : w.IsNontrivial := ⟨algebraMap ℚ_[l] E l, by
    rw [valuationOfAlgebra_algebraMap]
    refine ⟨by simp [(Fact.out : l.Prime).ne_zero], fun h ↦ ?_⟩
    have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h
    simp [Padic.norm_p, (Fact.out : l.Prime).one_lt.ne'] at this⟩
  have : IsNontrivial E := (isNontrivial_iff_isNontrivial w).mpr inferInstance
  have : IsValuativeTopology E := by
    refine IsValuativeTopology.of_mem_nhds_zero_iff_vle w fun {s} ↦ ?_
    have hnorm (z : E) : ‖z‖ = (w z : ℝ) := rfl
    rw [Metric.mem_nhds_iff]
    constructor
    · rintro ⟨ε, hε, hs⟩
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ((l : ℝ)⁻¹) ^ n < ε :=
        exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
      let x : E := algebraMap ℚ_[l] E ((l : ℚ_[l]) ^ n)
      have hx : (w x : ℝ) = ((l : ℝ)⁻¹) ^ n := by
        simp only [w, x]
        rw [valuationOfAlgebra_algebraMap]
        simp [Padic.norm_p]
      have hx0 : w.restrict x ≠ 0 :=
        ((Valuation.restrict_pos_iff w x).mpr (NNReal.coe_pos.mp (hx ▸ by positivity))).ne'
      refine ⟨Units.mk0 _ hx0, fun z hz ↦ hs ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
      rw [mem_ball_zero_iff, hnorm]
      exact (NNReal.coe_lt_coe.mpr hz).trans_eq hx |>.trans hn
    · rintro ⟨γ, hγ⟩
      refine ⟨MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass w) γ.val,
        ?_, fun z hz ↦ hγ ?_⟩
      · exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr γ.ne_zero))
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, ← NNReal.coe_lt_coe,
        ← hnorm]
      simpa using hz
  have : IsNonarchimedeanLocalField E := {}
  have heq : 𝒪[E] = (integers l E).toSubring := by
    ext x
    exact (isEquiv (valuation E) w).le_one_iff_le_one
  let e : 𝒪[E] ≃+* integers l E := RingEquiv.subringCongr heq
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact (IsAdicComplete.congr_ringEquiv _ e).mpr inferInstance

/-- If `E` is a finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ`, the universe `u + 1` copy of its ring
of integers is `𝔪_E`-adically complete. Through `Ideal.isLimitQuotPowCone` this says that
the coefficient ring is the limit of the tower `n ↦ 𝒪_E / 𝔪_Eⁿ` of its reductions. -/
instance isAdicComplete_maximalIdealShrink [FiniteDimensional ℚ_[l] E] [Small.{u + 1} E] :
    IsAdicComplete (maximalIdealShrink l E) (Shrink.{u + 1} (integers l E)) :=
  (IsAdicComplete.congr_ringEquiv _ (shrinkRingEquiv l E)).mpr inferInstance

end Complete

end PadicAlgCl
