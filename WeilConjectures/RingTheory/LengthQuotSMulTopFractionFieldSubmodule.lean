/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.LocalRing.Defs

import Mathlib.RingTheory.OrderOfVanishing.Basic
import WeilConjectures.RingTheory.LengthQuotSMulTopFGFractionFieldSubmodule

/-!
# Bounded length for a fraction-field submodule modulo a scalar

Over a one-dimensional Noetherian local domain, any submodule `M` of `K^r` satisfies
`length(M/xM) ≤ r · length(R/xR)` for nonzero `x`; in particular this length is finite.

## Implementation details

The finite case is proved in `LengthQuotSMulTopFGFractionFieldSubmodule`. For arbitrary `M`,
representatives of the steps of a strict chain in `M/xM` span a finitely generated submodule
`M'` with a strict chain of the same length in `M'/xM'`, so the finite bound applies to every
chain.

## References

* [Stacks, Tag 00PE]
-/

@[expose] public section

universe u v

namespace Submodule

private theorem length_quotSMulTop_le_of_fg
    {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (x : R) (b : ℕ∞)
    (hfg : ∀ N : Submodule R V, N.FG → Module.length R (QuotSMulTop x N) ≤ b) :
    Module.length R (QuotSMulTop x V) ≤ b := by
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim_eq_iSup_length,
    WithBot.coe_le_coe, iSup_le_iff]
  intro p
  have hw (i : Fin p.length) :
      ∃ m : V, (Submodule.Quotient.mk m : QuotSMulTop x V) ∈ p i.succ ∧
        (Submodule.Quotient.mk m : QuotSMulTop x V) ∉ p (Fin.castSucc i) := by
    obtain ⟨q, hq, hq'⟩ := IsConcreteLE.exists_of_lt
      (show p (Fin.castSucc i) < p i.succ from p.step i)
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨m, hq, hq'⟩
  choose m hm hm' using hw
  let N : Submodule R V := Submodule.span R (Set.range m)
  have hN : N.FG := Submodule.fg_span (Set.finite_range m)
  let f : QuotSMulTop x N →ₗ[R] QuotSMulTop x V := QuotSMulTop.map x N.subtype
  let q : LTSeries (Submodule R (QuotSMulTop x N)) :=
    { length := p.length
      toFun := fun i ↦ (p i).comap f
      step := fun i ↦ by
        apply lt_of_le_of_ne (Submodule.comap_mono (p.step i).le)
        intro he
        let z : N := ⟨m i, Submodule.subset_span (Set.mem_range_self i)⟩
        have hz : (Submodule.Quotient.mk z : QuotSMulTop x N) ∈
            (p i.succ).comap f := hm i
        have hz' : (Submodule.Quotient.mk z : QuotSMulTop x N) ∉
            (p (Fin.castSucc i)).comap f := hm' i
        exact hz' (he ▸ hz) }
  have hq : (q.length : ℕ∞) ≤ Module.length R (QuotSMulTop x N) := by
    rw [← WithBot.coe_le_coe, Module.coe_length]
    exact Order.LTSeries.length_le_krullDim q
  exact hq.trans (hfg N hN)

/-- Over a one-dimensional Noetherian local domain, reduction of any submodule of a finite
power of the fraction field modulo a nonzero scalar has bounded finite length. -/
theorem length_quotSMulTop_le_of_ringKrullDim_eq_one_of_isLocalRing
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ≠ 0) :
    Module.length R (QuotSMulTop x R) < ⊤ ∧
      Module.length R (QuotSMulTop x M) < ⊤ ∧
      Module.length R (QuotSMulTop x M) ≤ (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [hdim])
  have hlen : Module.length R (QuotSMulTop x R) < ⊤ := by
    have hfin := isFiniteLength_quotient_span_singleton R
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
    have he : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
      Submodule.quotEquivOfEq _ _ (by simp [← Submodule.ideal_span_singleton_smul])
    rw [he.length_eq]
    exact (Module.length_ne_top_iff.mpr hfin).lt_top
  have hbound : Module.length R (QuotSMulTop x M) ≤
      (r : ℕ∞) * Module.length R (QuotSMulTop x R) := by
    apply length_quotSMulTop_le_of_fg
    intro N hN
    let e := Submodule.equivMapOfInjective M.subtype M.subtype_injective N
    rw [(QuotSMulTop.congr x e).length_eq]
    exact length_quotSMulTop_le_of_fg_of_ringKrullDim_eq_one_of_isLocalRing
      r (N.map M.subtype) (hN.map _) hdim x hx
  exact ⟨hlen, lt_of_le_of_lt hbound (WithTop.mul_lt_top (ENat.natCast_lt_top r) hlen), hbound⟩

end Submodule

