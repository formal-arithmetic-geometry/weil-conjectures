/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Regular.Free
public import WeilConjectures.RingTheory.DiscreteValuationRing.FiniteKummerLevel

/-!
# `𝒪_E / ϖ^n` is free over `ℤ / ℓ^N`

Let `R` be a discrete valuation ring which is a finite `ℤ_ℓ`-algebra (for instance the valuation
ring `𝒪_E` of a finite extension `E` of `ℚ_ℓ`), with uniformizer `ϖ`, and let `ℓ = (unit) · ϖ^e`
with `e ≥ 1`. We show:

* `R` is free over `ℤ_ℓ` of rank `e f`, where `e` is the ramification index and `f` the inertia
  degree of `R` over `ℤ_ℓ` (`IsDiscreteValuationRing.finrank_padicInt_eq`);
* for every `N ≥ 1`, `A = R / ϖ^{e N} = R / ℓ^N` is free of rank `e f` over `ℤ / ℓ^N`
  (`IsDiscreteValuationRing.free_zmod_quotient_span_pow`).

This is the freeness clause of blueprint `lem-pur-finite-kummer-level`.
-/

@[expose] public section

open IsLocalRing
open scoped Pointwise

namespace IsDiscreteValuationRing

variable {ℓ : ℕ} {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  (hϖ : Irreducible ϖ) {e : ℕ} (he : 0 < e) (hℓe : Associated (ℓ : R) (ϖ ^ e))

omit [IsDiscreteValuationRing R] in
include hϖ hℓe in
lemma natCast_ne_zero_of_associated : (ℓ : R) ≠ 0 := by
  obtain ⟨v, hv⟩ := hℓe
  intro h
  rw [h, zero_mul] at hv
  exact pow_ne_zero _ hϖ.ne_zero hv.symm

include hϖ he hℓe in
lemma natCast_mem_maximalIdeal_of_associated : (ℓ : R) ∈ maximalIdeal R := by
  obtain ⟨v, hv⟩ := hℓe
  have hℓv : (ℓ : R) = ϖ ^ e * ↑v⁻¹ := by rw [← hv, mul_assoc, Units.mul_inv, mul_one]
  rw [hℓv]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖ.not_isUnit e he)

variable [hℓ : Fact ℓ.Prime] [Algebra ℤ_[ℓ] R]

include hϖ hℓe in
/-- The structure map `ℤ_ℓ → R` is injective. -/
lemma algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[ℓ] R) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible h0 PadicInt.irreducible_p
  rw [map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero (u.isUnit.map _).ne_zero
    (pow_ne_zero _ (natCast_ne_zero_of_associated hϖ hℓe)) hx

include hϖ hℓe in
/-- A discrete valuation ring which is a finite `ℤ_ℓ`-algebra (with `ℓ ≠ 0` in it) is free. -/
lemma free_padicInt [Module.Finite ℤ_[ℓ] R] : Module.Free ℤ_[ℓ] R := by
  have : Module.IsTorsionFree ℤ_[ℓ] R :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_padicInt_injective hϖ hℓe)
  infer_instance

include hϖ he hℓe in
lemma liesOver_maximalIdeal_padicInt : (maximalIdeal R).LiesOver (maximalIdeal ℤ_[ℓ]) := by
  refine ⟨(maximalIdeal.isMaximal ℤ_[ℓ]).eq_of_le
    (Ideal.comap_ne_top _ (maximalIdeal.isMaximal R).ne_top) ?_⟩
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
  change (ℓ : ℤ_[ℓ]) ∈ Ideal.comap (algebraMap ℤ_[ℓ] R) (maximalIdeal R)
  rw [Ideal.mem_comap, map_natCast]
  exact natCast_mem_maximalIdeal_of_associated hϖ he hℓe

include hϖ hℓe in
/-- The only prime of `R` over the maximal ideal of `ℤ_ℓ` is the maximal ideal of `R`. -/
lemma eq_maximalIdeal_of_mem_primesOver {q : Ideal R}
    (hq : q ∈ (maximalIdeal ℤ_[ℓ]).primesOver R) : q = maximalIdeal R := by
  obtain ⟨hqp, hqo⟩ := hq
  have hmem : (ℓ : ℤ_[ℓ]) ∈ q.under ℤ_[ℓ] := by
    rw [← hqo.over, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span rfl
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at hmem
  have hne : q ≠ ⊥ := fun h ↦ natCast_ne_zero_of_associated hϖ hℓe (by simpa [h] using hmem)
  exact eq_maximalIdeal (hqp.isMaximal hne)

include hϖ hℓe in
lemma map_maximalIdeal_padicInt :
    (maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] R) = maximalIdeal R ^ e := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
    hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  exact hℓe

include hϖ he hℓe in
/-- The ramification index of `R` over `ℤ_ℓ` is `e`. -/
theorem ramificationIdx_maximalIdeal_padicInt : (maximalIdeal R).ramificationIdx ℤ_[ℓ] = e := by
  have := liesOver_maximalIdeal_padicInt hϖ he hℓe
  have hmap := map_maximalIdeal_padicInt hϖ hℓe
  have hpS : (maximalIdeal ℤ_[ℓ]).map (algebraMap ℤ_[ℓ] R) ≠ ⊥ := by
    rw [hmap, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hϖ.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (maximalIdeal ℤ_[ℓ]) (maximalIdeal R) hpS]
  refine Ideal.ramificationIdx'_spec hmap.le fun h ↦ ?_
  rw [hmap, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
    Ideal.span_singleton_le_span_singleton, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at h
  omega

include hϖ he hℓe in
/-- The fundamental identity for `R / ℤ_ℓ`: `R` has rank `e f` over `ℤ_ℓ`, where `e` is the
ramification index and `f` the inertia degree of `R` over `ℤ_ℓ`. -/
theorem finrank_padicInt_eq [Module.Finite ℤ_[ℓ] R] :
    Module.finrank ℤ_[ℓ] R = e * (maximalIdeal R).inertiaDeg ℤ_[ℓ] := by
  have := free_padicInt hϖ hℓe
  have := liesOver_maximalIdeal_padicInt hϖ he hℓe
  have : Subsingleton ((maximalIdeal ℤ_[ℓ]).primesOver R) :=
    ⟨fun q q' ↦ Subtype.ext <| (eq_maximalIdeal_of_mem_primesOver hϖ hℓe q.2).trans
      (eq_maximalIdeal_of_mem_primesOver hϖ hℓe q'.2).symm⟩
  let : Fintype ((maximalIdeal ℤ_[ℓ]).primesOver R) := Fintype.ofFinite _
  have h := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal ℤ_[ℓ]) R
  rw [Fintype.sum_subsingleton _ ⟨maximalIdeal R, inferInstance, inferInstance⟩] at h
  rw [← h, ramificationIdx_maximalIdeal_padicInt hϖ he hℓe]

/-- `ℤ_ℓ / ℓ^N ≃ ℤ / ℓ^N`. -/
noncomputable def padicIntQuotientEquivZMod (N : ℕ) :
    ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ]) ^ N} ≃+* ZMod (ℓ ^ N) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow N).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))

lemma padicIntQuotientEquivZMod_mk (N : ℕ) (c : ℤ_[ℓ]) :
    padicIntQuotientEquivZMod N (Ideal.Quotient.mk _ c) = PadicInt.toZModPow N c :=
  rfl

/-- On an additive group killed by `ℓ^N`, the actions of `c : ℤ_ℓ` and of its image in
`ℤ / ℓ^N` agree. -/
lemma padicInt_smul_eq_toZModPow_smul {N : ℕ} {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M]
    [Module (ZMod (ℓ ^ N)) M] (hM : ∀ m : M, (ℓ ^ N) • m = 0) (c : ℤ_[ℓ]) (m : M) :
    c • m = PadicInt.toZModPow N c • m := by
  set k := (PadicInt.toZModPow N c).val
  have hk : PadicInt.toZModPow N c = (k : ZMod (ℓ ^ N)) := (ZMod.natCast_zmod_val _).symm
  have hck : c - k ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ N} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hk, sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hck
  rw [hk, Nat.cast_smul_eq_nsmul, show c = d * (ℓ : ℤ_[ℓ]) ^ N + k by rw [hd]; ring, add_smul,
    mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, hM, smul_zero, zero_add,
    Nat.cast_smul_eq_nsmul]

include hϖ he hℓe in
/-- Blueprint `lem-pur-finite-kummer-level`: Finite Kummer level of the Tate twist

The freeness clause: let `R = 𝒪_E` be a discrete valuation ring finite over `ℤ_ℓ`, with
uniformizer `ϖ` and `ℓ = (unit) · ϖ^e`, `e ≥ 1`, and let `N ≥ 1`. Then `A = R / ϖ^{e N}` (which equals
`R / ℓ^N`, `span_pow_mul_eq_span_natCast_pow`) is a free `ℤ / ℓ^N`-module of rank `e f`, where
`f` is the residue degree of `R` over `ℤ_ℓ`. The `ℤ / ℓ^N`-module structure on `A` is arbitrary
(it is unique, `A` having characteristic `ℓ^N`, `charP_quotient_span_pow`). -/
theorem free_zmod_quotient_span_pow [Module.Finite ℤ_[ℓ] R] {N : ℕ} (hN : 0 < N)
    [Module (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)})] :
    Module.Free (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) ∧
      Module.finrank (ZMod (ℓ ^ N)) (R ⧸ Ideal.span {ϖ ^ (e * N)}) =
        e * (maximalIdeal R).inertiaDeg ℤ_[ℓ] := by
  have := free_padicInt hϖ hℓe
  have := charP_quotient_span_pow hϖ hℓ.out he hℓe N
  set A := R ⧸ Ideal.span {ϖ ^ (e * N)}
  set x : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ N
  set T := ℤ_[ℓ] ⧸ Ideal.span {x}
  have hI : x • (⊤ : Submodule ℤ_[ℓ] R) =
      (Ideal.span {ϖ ^ (e * N)}).restrictScalars ℤ_[ℓ] := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map, Ideal.map_span,
      Set.image_singleton, map_pow, map_natCast, span_pow_mul_eq_span_natCast_pow hℓe]
  let j : QuotSMulTop x R ≃ₗ[ℤ_[ℓ]] A := Submodule.quotEquivOfEq _ _ hI ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv ℤ_[ℓ] (Ideal.span {ϖ ^ (e * N)})
  let iT : T ≃+* ZMod (ℓ ^ N) := padicIntQuotientEquivZMod N
  have : Fact (1 < ℓ ^ N) := ⟨Nat.one_lt_pow hN.ne' hℓ.out.one_lt⟩
  have : Nontrivial T := iT.toEquiv.nontrivial
  have hA : ∀ a : A, (ℓ ^ N) • a = 0 := fun a ↦ by
    rw [nsmul_eq_mul, Nat.cast_pow, ← Nat.cast_pow, CharP.cast_eq_zero, zero_mul]
  have hc : ∀ (t : T) (m : QuotSMulTop x R), j (t • m) = iT t • j m := by
    intro t m
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    change j (c • Submodule.Quotient.mk r) = _
    rw [map_smul, padicIntQuotientEquivZMod_mk]
    exact padicInt_smul_eq_toZModPow_smul hA c _
  -- `R / ℓ^N R` is free of rank `finrank ℤ_ℓ R` over `ℤ_ℓ / ℓ^N`
  have hfr : Module.finrank T (QuotSMulTop x R) = Module.finrank ℤ_[ℓ] R :=
    (((QuotSMulTop.equivQuotTensor x R).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective).finrank_eq).trans (Module.finrank_baseChange)
  refine ⟨?_, ?_⟩
  · have := RingHomInvPair.of_ringEquiv iT
    have := RingHomInvPair.symm (iT : T →+* ZMod (ℓ ^ N)) (iT.symm : ZMod (ℓ ^ N) →+* T)
    let e₂ : QuotSMulTop x R ≃ₛₗ[(iT : T →+* ZMod (ℓ ^ N))] A :=
      { j.toAddEquiv with map_smul' := hc }
    exact Module.Free.of_equiv e₂
  · rw [← finrank_padicInt_eq hϖ he hℓe, ← hfr]
    exact congrArg Cardinal.toNat
      (rank_eq_of_equiv_equiv iT j.toAddEquiv iT.bijective hc).symm

end IsDiscreteValuationRing
