/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Expand
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.RingTheory.FiniteModuleComplete

/-!
# Completed differentials and pth-power formal parameters

Source: EGA 0_IV, Lemma 21.9.4, using the module-finite special case;
ILO IV 2.1.6, the identification before (2.b)
(blueprint: lem-per-pth-power-series-completed-differential-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace KaehlerDifferential

/-- Completed differentials over `F` identify canonically with ordinary differentials
over the subalgebra of series in the pth powers of the parameters. The subalgebra is
the range of `expand p hp`, which fixes coefficients and multiplies every exponent by `p`.
The equivalence is characterized on universal differentials, so its underlying map is
precisely the map induced by the completed derivation in the first conjunct.

Source: EGA 0_IV, Lemma 21.9.4; ILO IV 2.1.6, before (2.b)
(blueprint: lem-per-pth-power-series-completed-differential-comparison).

Proof:
1. Finiteness over the power series ring makes the residue field finite over `F`.
Apply `lem-per-completed-differential-finite-conormal` to obtain finiteness of the
completed differential module, generation by completed differentials, and its
universal property for derivations into finite complete modules.
2. The power series ring is finite free over the pth-power parameter subalgebra,
with the monomials having all exponents less than `p` as basis. Hence `C` is finite
over that subalgebra and its relative differential module is finite over `C`.
Use `lem-weil-pbc-finite-module-complete-over-complete-noetherian` for completeness.
3. The completed derivation kills coefficients and pth powers in characteristic `p`.
Truncate a series in the subalgebra modulo the `N`th power of the variables ideal.
Locality sends the remainder into the `N`th power of the maximal ideal, whose
derivative lies in its `(N-1)`st power times the completion. Separatedness of the
inverse limit shows that the completed derivation kills the entire subalgebra.
The universal property of ordinary differentials gives the canonical forward map.
4. The relative derivation has finite complete target by step 2, so the completed
universal property in step 1 gives the reverse map.
5. Both composites fix the corresponding universal differentials. These generate
the two modules, so the maps are inverse. -/
theorem pth_power_series_completed_differential_comparison
    (F : Type u) [Field F] (p : ℕ) [CharP F p] (hp : p ≠ 0) (r : ℕ)
    (C : Type v) [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Algebra F C] [Algebra (MvPowerSeries (Fin r) F) C]
    [IsScalarTower F (MvPowerSeries (Fin r) F) C]
    [IsLocalHom (algebraMap (MvPowerSeries (Fin r) F) C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    [Module.Finite (MvPowerSeries (Fin r) F) C]
    (hcont : @Continuous (MvPowerSeries (Fin r) F) C
      (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin r) (R := F)))).adicTopology
      (IsLocalRing.maximalIdeal C).adicTopology (algebraMap (MvPowerSeries (Fin r) F) C)) :
    (∀ b : (MvPowerSeries.expand (σ := Fin r) (R := F) p hp).range,
      AdicCompletion.of (IsLocalRing.maximalIdeal C) (KaehlerDifferential F C)
        (KaehlerDifferential.D F C
          (algebraMap (MvPowerSeries (Fin r) F) C b.val)) = 0) ∧
    ∃ e : KaehlerDifferential (MvPowerSeries.expand (σ := Fin r) (R := F) p hp).range C
        ≃ₗ[C] AdicCompletion (IsLocalRing.maximalIdeal C) (KaehlerDifferential F C),
      ∀ c : C,
        e (KaehlerDifferential.D
          (MvPowerSeries.expand (σ := Fin r) (R := F) p hp).range C c) =
          AdicCompletion.of (IsLocalRing.maximalIdeal C) (KaehlerDifferential F C)
            (KaehlerDifferential.D F C c) := by
  sorry

end KaehlerDifferential
