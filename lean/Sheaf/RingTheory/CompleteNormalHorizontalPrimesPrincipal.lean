/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.MvPowerSeries.Inverse
import WeilConjectures.RingTheory.MvPowerSeriesQuotientKernel
import WeilConjectures.RingTheory.PowerSeriesCompleteOverCompleteBase
import WeilConjectures.RingTheory.PowerSeriesNormalDomain

/-!
# Horizontal height-one primes over a complete normal local domain

Source: EGA IV4, proof of Theorem 21.14.1, the complete power-series case
(blueprint: lem-sfb-complete-normal-horizontal-primes-principal).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MvPowerSeries

/-- A height-one prime of `C[[T₁, …, T_d]]` not contained in the extension of the maximal
ideal of a complete Noetherian normal local domain `C` has a nonzero generator.

Source: EGA IV4, proof of Theorem 21.14.1, complete power-series case; Bourbaki,
Algèbre commutative VII, §3, no. 7, Lemma 3 and no. 8, Propositions 5–6
(blueprint: lem-sfb-complete-normal-horizontal-primes-principal).

Proof:
1. For `d = 0`, every proper prime is contained in the maximal ideal of `C`, so the
   horizontal hypothesis is impossible. Otherwise regroup the variables as `A[[t]]`,
   with `A = C[[T₁, …, T_{d-1}]]`. Iterating
   `lem-weil-pbc-power-series-normal-domain` gives a Noetherian normal domain `A`.
   By `lem-weil-pbc-power-series-local-ring` its maximal ideal is the sum of the extended
   maximal ideal of `C` and the ideal of the first `d-1` variables. By
   `lem-weil-pbc-power-series-complete-over-complete-base`, `A` is complete for this ideal.
2. Choose `f` in `r` outside the extended maximal ideal. Since the maximal ideal of `C`
   is finitely generated, `lem-sbc-mv-power-series-quotient-kernel` says that the reduction
   of `f` is nonzero. By `lem-sfb-power-series-axis-coordinate-change`, change coordinates
   so that the resulting series `g` has nonzero reduction along the last axis. The image
   `q` of `r` remains a height-one prime, and `g` has nonzero image in `(A/m)[[t]]`.
3. By `lem-per-weierstrass-preparation-complete-local`, write `g = u * F` with `u` a unit
   and `F` a monic distinguished polynomial. Thus `F` lies in `q` and is not `1`.
4. By `lem-sfb-normal-domain-monic-prime-factorization`, factor `F` into monic
   positive-degree distinguished polynomials whose polynomial quotients are nonzero
   domains. Primality of `q` puts one factor `h` in `q`.
5. By `lem-per-distinguished-polynomial-quotient`, the power-series quotient by `h` is
   its polynomial quotient, hence a nonzero domain. Thus `(h)` is prime. Monicity gives
   `h ≠ 0`, so `(0) < (h) ≤ q`; height one forces `(h) = q`. Pulling back by the
   coordinate automorphism gives a nonzero generator of `r`. -/
theorem exists_nonzero_generator_of_height_one_of_not_le_extended_maximalIdeal
    (C : Type u) [CommRing C] [IsNoetherianRing C] [IsDomain C]
    [IsIntegrallyClosed C] [IsLocalRing C]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (d : ℕ) (r : Ideal (MvPowerSeries (Fin d) C)) (hr : r.IsPrime)
    (hr0 : r ≠ ⊥)
    (hheight : ∀ p : Ideal (MvPowerSeries (Fin d) C), p.IsPrime → ⊥ < p → p < r → False)
    (horiz : ¬ r ≤ (IsLocalRing.maximalIdeal C).map (MvPowerSeries.C (σ := Fin d))) :
    ∃ h : MvPowerSeries (Fin d) C, h ≠ 0 ∧ r = Ideal.span {h} := by
  sorry

end MvPowerSeries
