/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Positive finite length for a module supported at the maximal ideal

Source: Stacks Project, Algebra, Lemma 10.62.3 (Tag 00L5)
(blueprint: lem-sc-generic-stalk-finite-length).
-/

@[expose] public section

universe u v

namespace Module

/-- A nonzero finite module over a Noetherian local ring whose support is contained in
its maximal ideal has positive finite length. Source: Stacks Project, Algebra, Tag 00L5
(blueprint: lem-sc-generic-stalk-finite-length).

Proof: Let `J` be the annihilator of `M`. A prime of `R / J` pulls back to a
prime in the support of `M`, by `Module.mem_support_iff_of_finite`, so its pullback
is the maximal ideal. Consequently every prime of `R / J` is maximal. This quotient
is Noetherian of Krull dimension at most zero, hence Artinian. The canonical action
of `R / J` makes `M` a finite module over this Artinian ring, so it is Artinian.
Restriction of scalars along the surjective quotient map preserves this property.
Together with Noetherianness, this makes `Module.length R M` finite; nontriviality
makes it positive. -/
theorem length_eq_nat_of_support_subset_maximalIdeal
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h_support : ∀ p ∈ Module.support R M, p.asIdeal = IsLocalRing.maximalIdeal R) :
    ∃ n : ℕ, 0 < n ∧ Module.length R M = (n : ℕ∞) := by
  let J := Module.annihilator R M
  have : Ring.KrullDimLE 0 (R ⧸ J) := by
    refine Ring.krullDimLE_zero_iff.mpr fun p hp ↦ ?_
    have hcomap : (p.comap (Ideal.Quotient.mk J)).IsPrime :=
      hp.comap (Ideal.Quotient.mk J)
    have hmem : (⟨p.comap (Ideal.Quotient.mk J), hcomap⟩ : PrimeSpectrum R) ∈
        Module.support R M := by
      apply Module.mem_support_iff_of_finite.mpr
      exact (by simp : J ≤ RingHom.ker (Ideal.Quotient.mk J)).trans (Ideal.ker_le_comap _)
    have hmax : (p.comap (Ideal.Quotient.mk J)).IsMaximal := by
      have heq : p.comap (Ideal.Quotient.mk J) = IsLocalRing.maximalIdeal R :=
        h_support _ hmem
      rw [heq]
      exact IsLocalRing.maximalIdeal.isMaximal R
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p hmax
  have : IsArtinianRing (R ⧸ J) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let : Module (R ⧸ J) M := Module.quotientAnnihilator
  have : IsScalarTower R (R ⧸ J) M :=
    Module.IsTorsionBySet.isScalarTower (Module.isTorsionBySet_annihilator R M)
  have : Module.Finite (R ⧸ J) M := Module.Finite.of_restrictScalars_finite R (R ⧸ J) M
  have : IsArtinian R M :=
    (Module.isTorsionBySet_annihilator R M).semilinearMap.isArtinian_iff_of_bijective
      Function.bijective_id |>.mpr inferInstance
  have hfin : Module.length R M ≠ ⊤ := Module.length_ne_top
  exact ⟨(Module.length R M).toNat,
    ENat.toNat_pos (Module.length_pos.ne') hfin, (ENat.natCast_toNat hfin).symm⟩

end Module
