/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Basic
import WeilConjectures.RingTheory.DepthLeSupportDimension
import Mathlib.RingTheory.Depth.Rees
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.Regular.Category

/-!
# Depth drops by one modulo a regular element

For a nonzero finite module `M` over a Noetherian local ring and a nonzerodivisor `x` on `M`
in the maximal ideal, `depth (M/xM) = depth M - 1`.

## Implementation details

The proof uses Ext and Rees' theorem rather than the depth-lemma argument of the source. With
`A_i = Ext^i(R/𝔪, M)` and `B_i = Ext^i(R/𝔪, M/xM)`, multiplication by `x` acts as zero on
`A_i`, so the long exact sequence splits into short exact sequences
`0 → A_i → B_i → A_{i+1} → 0`, which shift the first nonvanishing degree by one.

## References

* [Stacks, Tag 090R]
-/

@[expose] public section

universe u v

namespace IsLocalRing

private theorem regular_sequence_shorten_small {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    (n : ℕ) (rs : List R) (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : RingTheory.Sequence.IsRegular M rs) :
    ∃ qs : List R, qs.length = n ∧ (∀ r ∈ qs, r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop x M) qs := by
  let := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hM : maximalIdeal R • (⊤ : Submodule R M) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm.lt_top
  have hQ : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R (QuotSMulTop x M)))).symm.lt_top
  have hvan := ((ModuleCat.exists_isRegular_tfae (maximalIdeal R) (n + 1)
    (ModuleCat.of R M) hM).out 4 1 rfl rfl).mp ⟨rs, hlen, hmem, hrs⟩
  apply ((ModuleCat.exists_isRegular_tfae (maximalIdeal R) n
    (ModuleCat.of R (QuotSMulTop x M)) hQ).out 1 4 rfl rfl).mp
  intro N hN hNfin hsupp i hi
  let := hN
  let := hNfin
  exact AddCommGrpCat.subsingleton_of_isZero <|
    CategoryTheory.ShortComplex.Exact.isZero_of_both_zeros
      (CategoryTheory.Abelian.Ext.covariant_sequence_exact₃' N
        (IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg) i (i + 1) rfl)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (hvan N hN hNfin hsupp i (by omega))).eq_zero_of_src _)
      ((AddCommGrpCat.isZero_of_iff_subsingleton.mpr
        (hvan N hN hNfin hsupp (i + 1) (by omega))).eq_zero_of_tgt _)

private theorem regular_sequence_shorten {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    (n : ℕ) (rs : List R) (hlen : rs.length = n + 1)
    (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R) (hrs : RingTheory.Sequence.IsRegular M rs) :
    ∃ qs : List R, qs.length = n ∧ (∀ r ∈ qs, r ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop x M) qs := by
  let := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  let e : ULift.{u} M ≃ₗ[R] M := ULift.moduleEquiv
  have hxreg : RingTheory.Sequence.IsRegular M [x] :=
    (RingTheory.Sequence.isRegular_cons_iff M x []).mpr
      ⟨hreg, by simp [RingTheory.Sequence.isRegular_iff]⟩
  have hlift : IsSMulRegular (ULift.{u} M) x :=
    ((RingTheory.Sequence.isRegular_cons_iff (ULift.{u} M) x []).mp
      ((e.isRegular_congr [x]).mpr hxreg)).1
  obtain ⟨qs, hlenq, hmemq, hregq⟩ :=
    regular_sequence_shorten_small (ULift.{u} M) x hx hlift n rs hlen hmem
      ((e.isRegular_congr rs).mpr hrs)
  refine ⟨qs, hlenq, hmemq, ?_⟩
  exact ((RingTheory.Sequence.isRegular_cons_iff M x qs).mp
    ((e.isRegular_congr (x :: qs)).mp
      ((RingTheory.Sequence.isRegular_cons_iff (ULift.{u} M) x qs).mpr ⟨hlift, hregq⟩))).2

/-- For a nonzero finite module over a Noetherian local ring, quotienting by a
nonzerodivisor in the maximal ideal gives a nonzero module and lowers the finite,
positive depth by one. -/
theorem depth_quotSMulTop_of_isSMulRegular {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (x : R) (hx : x ∈ maximalIdeal R)
    (hreg : IsSMulRegular M x) :
    Nontrivial (QuotSMulTop x M) ∧
      ∃ d : ℕ, 1 ≤ d ∧ depth (R := R) M = (d : ℕ∞) ∧
        depth (R := R) (QuotSMulTop x M) = ((d - 1 : ℕ) : ℕ∞) := by
  let := nontrivial_quotSMulTop_of_mem_maximalIdeal M hx
  have hM : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
  have hQ : maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R (QuotSMulTop x M)))).symm
  have hMdef : depth (R := R) M = sSup {n : ℕ∞ | ∃ rs : List R,
      RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        n = (rs.length : ℕ∞)} := by
    simp only [depth, Ideal.depth, ite_eq_right hM]
  have hQdef : depth (R := R) (QuotSMulTop x M) = sSup {n : ℕ∞ | ∃ rs : List R,
      RingTheory.Sequence.IsRegular (QuotSMulTop x M) rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        n = (rs.length : ℕ∞)} := by
    simp only [depth, Ideal.depth, ite_eq_right hQ]
  have hfinite : depth (R := R) M ≠ ⊤ := by
    intro heq
    have hbound := (depth_le_supportDim (R := R) M).trans
      (Module.supportDim_le_ringKrullDim R M)
    rw [heq] at hbound
    exact (ne_of_lt (ringKrullDim_lt_top (R := R))) (by simpa using hbound)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hxreg : RingTheory.Sequence.IsRegular M [x] :=
    (RingTheory.Sequence.isRegular_cons_iff M x []).mpr
      ⟨hreg, by simp [RingTheory.Sequence.isRegular_iff]⟩
  have hpos : 1 ≤ d := by
    have hone : (1 : ℕ∞) ≤ depth (R := R) M := by
      rw [hMdef]
      exact le_sSup ⟨[x], hxreg, by simpa using hx, rfl⟩
    rw [← hd] at hone
    exact_mod_cast hone
  refine ⟨inferInstance, d, hpos, hd.symm, le_antisymm ?_ ?_⟩
  · rw [hQdef]
    apply sSup_le
    rintro k ⟨rs, hrs, hmem, rfl⟩
    have hlen : ((rs.length + 1 : ℕ) : ℕ∞) ≤ depth (R := R) M := by
      rw [hMdef]
      exact le_sSup ⟨x :: rs, (RingTheory.Sequence.isRegular_cons_iff M x rs).mpr ⟨hreg, hrs⟩,
        by simpa using And.intro hx hmem, by simp⟩
    rw [← hd] at hlen
    have hlen' : rs.length + 1 ≤ d := by exact_mod_cast hlen
    exact_mod_cast (show rs.length ≤ d - 1 by omega)
  · have hsupmem : depth (R := R) M ∈ {n : ℕ∞ | ∃ rs : List R,
        RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
        n = (rs.length : ℕ∞)} := by
      rw [hMdef]
      have hempty : RingTheory.Sequence.IsRegular (R := R) M [] := by
        simp [RingTheory.Sequence.isRegular_iff]
      let : Nonempty {n : ℕ∞ | ∃ rs : List R,
          RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
            n = (rs.length : ℕ∞)} := ⟨⟨0, [], hempty, by simp, rfl⟩⟩
      apply ENat.sSup_mem_of_nonempty_of_lt_top
      simpa only [← hMdef] using hfinite.lt_top
    obtain ⟨rs, hrs, hmem, hlen⟩ := hsupmem
    have hlen' : rs.length = d := by
      rw [← hd] at hlen
      exact_mod_cast hlen.symm
    obtain ⟨qs, hlenq, hmemq, hregq⟩ :=
      regular_sequence_shorten M x hx hreg (d - 1) rs (by omega) hmem hrs
    rw [hQdef]
    exact le_sSup ⟨qs, hregq, hmemq, by simp [hlenq]⟩

end IsLocalRing
