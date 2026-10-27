/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.RingTheory.PowerSeriesUniversalPropertyComplete
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# Power-series presentations with prescribed coefficients and generators

Source: Stacks Project, Varieties, Tag 0C52, final proof paragraph, with the
coefficient section fixed in advance; Algebra, Tags 0315 and 0306.
(blueprint: lem-trf-coefficient-field-generator-presentation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MvPowerSeries

/-- A fixed coefficient section and any tuple generating the maximal ideal give a
continuous surjective power-series algebra map with finitely generated kernel.
The given `Algebra F R` encodes the section `σ` as `algebraMap F R`.

Source: Stacks Project, Varieties, Tag 0C52, final proof paragraph; Algebra,
Tags 0315 and 0306. (blueprint: lem-trf-coefficient-field-generator-presentation)

Proof:
1. Apply `lem-weil-pbc-power-series-universal-property-complete` with base `F`,
   target `R`, ideal its maximal ideal, coefficient map `algebraMap F R`, and
   parameters `y`. The constant values make the resulting ring map an algebra
   map. The variables ideal maps to the maximal ideal since the `y` generate it.
   Its powers map into the corresponding powers, which proves adic continuity.
2. The degree-one congruence gives `ρ (π (Φ g)) = constantCoeff g` by the section
   identity. By `lem-weil-pbc-power-series-combined-ideal-coefficients` with base
   ideal zero and power one, the constant coefficient vanishes exactly on the
   variables ideal. Injectivity of `ρ` identifies this ideal with the inverse
   image of the maximal ideal.
3. A field is Noetherian and complete for the zero ideal, so
   `lem-weil-pbc-power-series-complete-over-complete-base` makes the source
   complete for the variables ideal. Target completeness includes Hausdorffness.
   The composite to the target residue field is surjective: the constant `ρ b`
   lifts every residue class `b`. Now
   `lem-weil-pbc-complete-source-surjective-mod-ideal` gives surjectivity of `Φ`.
4. By `lem-weil-pbc-power-series-noetherian`, the source is Noetherian. Thus its
   kernel has a finite generating tuple. Every generator lies in the kernel,
   hence in the inverse image of the maximal ideal, already identified with the
   variables ideal. The tuple can be empty for zero kernel. With zero variables,
   the generator hypothesis forces the maximal ideal to vanish; the section is
   then an isomorphism, giving the same conclusion with an empty kernel tuple.
-/
theorem exists_coefficientField_generator_presentation
    (F : Type u) (R : Type v) [Field F] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [Algebra F R] (ρ : (R ⧸ IsLocalRing.maximalIdeal R) ≃+* F)
    (hσ : ∀ c : F, ρ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      (algebraMap F R c)) = c)
    (n : ℕ) (y : Fin n → R)
    (hy : ∀ i : Fin n, y i ∈ IsLocalRing.maximalIdeal R)
    (hgen : Ideal.span (Set.range y) = IsLocalRing.maximalIdeal R) :
    ∃ Φ : MvPowerSeries (Fin n) F →ₐ[F] R,
      Function.Surjective Φ ∧
      (∀ i : Fin n, Φ (MvPowerSeries.X i) = y i) ∧
      (∀ c : F, Φ (MvPowerSeries.C c) = algebraMap F R c) ∧
      @Continuous (MvPowerSeries (Fin n) F) R
        (Ideal.span (Set.range
          (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F))).adicTopology
        (IsLocalRing.maximalIdeal R).adicTopology Φ ∧
      Ideal.comap Φ.toRingHom (IsLocalRing.maximalIdeal R) =
        Ideal.span (Set.range
          (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F)) ∧
      ∃ (s : ℕ) (f : Fin s → MvPowerSeries (Fin n) F),
        (∀ j : Fin s, f j ∈ Ideal.span (Set.range
          (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F))) ∧
        Ideal.span (Set.range f) = RingHom.ker Φ.toRingHom := by
  sorry

end MvPowerSeries
