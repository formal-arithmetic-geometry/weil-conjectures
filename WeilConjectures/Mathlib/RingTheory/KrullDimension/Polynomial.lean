/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Krull dimension of finitely generated algebras and of quotients

## Main results

- `ringKrullDim_ne_top_of_finiteType`: a finitely generated algebra over a field has finite Krull
  dimension.
- `Ideal.eq_of_le_of_ringKrullDim_quotient_eq`: if `I ≤ J` with `I` prime and `R ⧸ I` of finite
  dimension, then `R ⧸ J` has the dimension of `R ⧸ I` only if `J = I`: a proper closed subset
  of an irreducible variety has smaller dimension.
-/

@[expose] public section

/-- A finitely generated algebra over a field has finite Krull dimension. -/
theorem ringKrullDim_ne_top_of_finiteType (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType k A›
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_le_of_surjective f.toRingHom hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  intro h
  cases h

/-- A proper closed subset of an irreducible closed subset of `Spec R` of finite dimension has
strictly smaller dimension: if `I ≤ J` with `I` prime, `R ⧸ I` finite-dimensional and
`dim (R ⧸ J) = dim (R ⧸ I)`, then `J = I`. -/
theorem Ideal.eq_of_le_of_ringKrullDim_quotient_eq {R : Type*} [CommRing R] {I J : Ideal R}
    [hI : I.IsPrime] (hIJ : I ≤ J) (hfin : ringKrullDim (R ⧸ I) ≠ ⊤)
    (h : ringKrullDim (R ⧸ J) = ringKrullDim (R ⧸ I)) : J = I := by
  by_contra hne
  have hlt : I < J := lt_of_le_of_ne hIJ (Ne.symm hne)
  rw [ringKrullDim_quotient, ringKrullDim_quotient] at h
  rw [ringKrullDim_quotient] at hfin
  have hbot : Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) ≠ ⊥ :=
    Order.krullDim_ne_bot_iff.2 ⟨⟨⟨I, hI⟩, fun _ h ↦ h⟩⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) = d := by
    rcases hk : Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) with _ | _ | d
    · exact absurd hk hbot
    · exact absurd hk hfin
    · exact ⟨d, rfl⟩
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (h.trans hd).ge
  let f : PrimeSpectrum.zeroLocus (R := R) J → PrimeSpectrum.zeroLocus (R := R) I :=
    fun x ↦ ⟨x.1, (PrimeSpectrum.zeroLocus_anti_mono hIJ) x.2⟩
  have hf : StrictMono f := fun _ _ h ↦ h
  let l' := (l.map f hf).cons ⟨⟨I, hI⟩, fun _ h ↦ h⟩ (by
    change I < (l.head : PrimeSpectrum R).asIdeal
    exact lt_of_lt_of_le hlt l.head.2)
  have := Order.LTSeries.length_le_krullDim l'
  rw [hd, RelSeries.cons_length, LTSeries.map_length, hl] at this
  exact absurd (WithBot.coe_le_coe.1 this) (by norm_cast; omega)
