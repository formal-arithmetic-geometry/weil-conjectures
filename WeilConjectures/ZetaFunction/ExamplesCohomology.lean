/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Endpoints
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.TateTwistCohomology
public import WeilConjectures.ZetaFunction.Examples
public import WeilConjectures.ZetaFunction.Weights

/-!
# Compactly supported cohomology of the affine line and of the multiplicative group

Let `C₀` be a smooth geometrically connected affine curve over the finite field `k₀ = 𝔽_q`. The
compactly supported cohomology `H_cⁱ(C₀ ⊗ k̄, ℚ̄_ℓ)` vanishes outside degrees `1` and `2`, is
`ι`-pure of weight `2` in degree `2` and `ι`-mixed of weights at most `1` in degree `1`. Together
with the Grothendieck–Lefschetz trace formula this determines it from the point counts when they
are as simple as those of `𝔸¹` and `𝔾_m`:

* `H_c²(𝔸¹ ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` and all other `H_cⁱ` vanish (blueprint `ex-weil-affine-line`);
* `H_c¹(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ`, `H_c²(𝔾_m ⊗ k̄, ℚ̄_ℓ) ≅ ℚ̄_ℓ(-1)` and all other `H_cⁱ` vanish
  (blueprint `ex-weil-multiplicative-group`).

Indeed the reciprocal roots of `det(1 - T F | H_c²)` have absolute value `q` under every
embedding `ι`, those of `det(1 - T F | H_c¹)` at most `q^{1/2}`, and the trace formula gives
`Z(C₀, T) det(1 - T F | H_c²) = det(1 - T F | H_c¹)`; comparing with `Z(𝔸¹, T) = (1 - qT)⁻¹` and
`Z(𝔾_m, T) = (1 - T)/(1 - qT)` leaves no room for cancellation.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_curve`,
  `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two_adicConstant`:
  vanishing and purity for a smooth geometrically connected affine curve.
- `AlgebraicGeometry.compactlySupportedCohomology_affineLine`: `ex-weil-affine-line`.
- `AlgebraicGeometry.compactlySupportedCohomology_multiplicativeGroup`:
  `ex-weil-multiplicative-group`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]

/-- A smooth curve over `k₀` is locally of finite type over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

variable (k₀ l C)

/-- The compactly supported cohomology of the constant Weil sheaf on a smooth geometrically
connected affine curve vanishes outside degrees `1` and `2`: the pushforward of the constant sheaf
along the identity is the constant sheaf (`AlgebraicGeometry.WeilSheaf.lowerStarIdIso`), so this
is the case `j = 𝟙` of `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage`
and `AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`. -/
theorem subsingleton_compactlySupportedCohomology_adicConstant_of_curve {r : ℤ} (hr : r ≠ 1)
    (hr' : r ≠ 2) :
    Subsingleton ((adicConstant k₀ l C).compactlySupportedCohomology r).carrier := by
  have e := (compactlySupportedCohomologyEquivOfIso (lowerStarIdIso (adicConstant k₀ l C)) r)
  have hF := isLisse_adicConstant k₀ l C
  rcases lt_trichotomy r 0 with h | rfl | h
  · have := subsingleton_compactlySupportedCohomology_directImage (𝟙 C) _ hF (r := r) (Or.inl h)
    exact e.toLinearEquiv.symm.subsingleton
  · have := subsingleton_compactlySupportedCohomology_directImage_zero (𝟙 C) _ hF
    exact e.toLinearEquiv.symm.subsingleton
  · have := subsingleton_compactlySupportedCohomology_directImage (𝟙 C) _ hF (r := r)
      (Or.inr (by omega))
    exact e.toLinearEquiv.symm.subsingleton

/-- The top compactly supported cohomology `H_c²(C₀ ⊗ k̄, ℚ̄_ℓ)` of a smooth geometrically
connected affine curve is `ι`-pure of weight `2`: this is the case `j = 𝟙` of
`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`, the constant
sheaf being lisse and punctually pure of weight `0`. -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_adicConstant
    (ι : PadicAlgCl l →+* ℂ) :
    ((adicConstant k₀ l C).compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι 2 := by
  have e := (compactlySupportedCohomologyEquivOfIso (lowerStarIdIso (adicConstant k₀ l C)) 2)
  have h := isPureOfWeightOver_compactlySupportedCohomology_directImage_two (j := 𝟙 C)
    (F := adicConstant k₀ l C) ι (isLisse_adicConstant k₀ l C) (isPunctuallyPureOfWeight_adicConstant k₀ l C ι)
  rw [zero_add] at h
  exact fun α hα ↦ h α (e.symm.hasEigenvalue hα)

variable [IsSeparated (C ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]

/-- The trace formula on a smooth geometrically connected affine curve `C₀`: since the compactly
supported cohomology is concentrated in degrees `1` and `2`,
`Z(C₀, T) det(1 - T F | H_c²) = det(1 - T F | H_c¹)` in `ℚ̄_ℓ⟦T⟧`. This is the trace-to-determinant
identity of a trace datum (`TraceDatum.zeta_mul_prod_even_eq_prod_odd`) formed by the groups
`H_c⁰, H_c¹, H_c²`, the first of which vanishes. -/
theorem map_zetaSeries_mul_charpolyRev_two_of_curve :
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (C ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (((adicConstant k₀ l C).compactlySupportedCohomology 2).frobeniusEnd.charpolyRev :
          PowerSeries (PadicAlgCl l)) =
      (((adicConstant k₀ l C).compactlySupportedCohomology 1).frobeniusEnd.charpolyRev :
        PowerSeries (PadicAlgCl l)) := by
  set H := (adicConstant k₀ l C).compactlySupportedCohomology
  have hvan (i : ℤ) (h1 : i ≠ 1) (h2 : i ≠ 2) : Subsingleton (H i).carrier :=
    subsingleton_compactlySupportedCohomology_adicConstant_of_curve k₀ l C h1 h2
  let D : TraceDatum.{0, u + 1} (PadicAlgCl l) 2 :=
    { V := fun i ↦ (H (i : ℕ)).carrier
      F := fun i ↦ (H (i : ℕ)).frobeniusEnd
      N := fun n ↦ ((C ↘ Spec (CommRingCat.of k₀)).pointCount n : ℤ)
      trace_eq := fun n hn ↦ by
        rw [Int.cast_natCast, pointCount_eq_finsum_trace_compactlySupportedCohomology k₀ l C hn,
          finsum_eq_sum_of_support_subset (s := (Finset.range 3).map Nat.castEmbedding) _ ?_,
          Finset.sum_map, Finset.sum_range]
        · refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Nat.castEmbedding_apply, Int.coe_negOnePow_natCast, zsmul_eq_mul]
          push_cast
          rfl
        · intro i hi
          by_contra h
          have hi' : i ≠ 1 ∧ i ≠ 2 := by
            constructor <;> rintro rfl <;> exact h (Finset.mem_map.2 ⟨_, Finset.mem_range.2
              (by norm_num : _ < 3), rfl⟩)
          have := hvan i hi'.1 hi'.2
          exact hi (by
            dsimp only
            rw [Subsingleton.elim ((H i).frobeniusEnd ^ n) 0, map_zero, smul_zero]) }
  have hZ : PowerSeries.map (algebraMap ℚ (PadicAlgCl l))
      (C ↘ Spec (CommRingCat.of k₀)).zetaSeries = D.zeta := D.map_zetaSeries _ fun _ ↦ rfl
  have key := D.zeta_mul_prod_even_eq_prod_odd
  have he : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Even (i : ℕ)) = {0, 2} := by decide
  have ho : Finset.univ.filter (fun i : Fin (2 + 1) ↦ Odd (i : ℕ)) = {1} := by decide
  rw [he, ho, Finset.prod_pair (by decide), Finset.prod_singleton] at key
  have hP0 : D.P 0 = 1 := by
    have : Subsingleton (D.V 0) := hvan 0 (by decide) (by decide)
    exact LinearMap.charpolyRev_of_subsingleton _
  rw [hP0, Polynomial.coe_one, one_mul, ← hZ] at key
  exact key

end WeilSheaf

end AlgebraicGeometry
