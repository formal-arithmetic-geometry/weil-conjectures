/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Krull dimension is invariant under integral extensions

If `S` is an integral `R`-algebra, then `dim S ≤ dim R`, and if moreover `R → S` is injective
then the two dimensions agree.

## Main results

* `Algebra.IsIntegral.ringKrullDim_le`: `dim S ≤ dim R` for an integral algebra. This is
  incomparability: two distinct comparable primes of `S` have distinct contractions, so
  contracting a chain of primes of `S` gives a chain of primes of `R` of the same length.
* `Algebra.IsIntegral.le_ringKrullDim`: `dim R ≤ dim S` for an integral algebra with `R → S`
  injective. This is lying over together with going up: a prime of `S` lies over the head of
  a given chain of primes of `R`, and going up extends it to a chain of the same length.
* `Algebra.IsIntegral.ringKrullDim_eq`: `dim S = dim R`, the conjunction of the two.
* `ringKrullDim_eq_of_isIntegral_of_injective`: the same statement for an injective integral
  ring homomorphism `f : R →+* S`.
* `Algebra.IsIntegral.ringKrullDim_quotient_eq`: `dim (S ⧸ P) = dim (R ⧸ P ∩ R)` for an integral
  algebra and an ideal `P` of `S`; the extension `R ⧸ P ∩ R ⊆ S ⧸ P` is again integral, and it is
  injective by construction.
-/

@[expose] public section

open Order

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- If `S` is an integral `R`-algebra, then `dim S ≤ dim R`.

Contracting along `algebraMap R S` is strictly monotone on primes by incomparability, so it
turns a chain of primes of `S` into a chain of primes of `R` of the same length. -/
@[stacks 00OJ]
theorem Algebra.IsIntegral.ringKrullDim_le [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h

/-- If `S` is an integral `R`-algebra and `algebraMap R S` is injective, then `dim R ≤ dim S`.

Given a chain of primes of `R`, lying over produces a prime of `S` above its smallest member,
and going up extends that prime to a chain of primes of `S` of the same length. -/
theorem Algebra.IsIntegral.le_ringKrullDim [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, hP⟩ := Ideal.nonempty_primesOver (S := S) (RelSeries.head l).asIdeal
  have : P.IsPrime := hP.1
  have : P.LiesOver (RelSeries.head l).asIdeal := hP.2
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact hlen ▸ L.length_le_krullDim

/-- The Krull dimension is invariant under an injective integral extension of rings. -/
@[stacks 00OK]
theorem Algebra.IsIntegral.ringKrullDim_eq [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm (Algebra.IsIntegral.ringKrullDim_le R S) (Algebra.IsIntegral.le_ringKrullDim R S)

/-- The Krull dimension is invariant under an injective integral ring homomorphism. -/
@[stacks 00OK]
theorem ringKrullDim_eq_of_isIntegral_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim R :=
  let _ : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  Algebra.IsIntegral.ringKrullDim_eq R S

/-- For an integral algebra `S` over `R` and an ideal `P` of `S`, the quotient `S ⧸ P` has the
same Krull dimension as `R ⧸ P ∩ R`. -/
theorem Algebra.IsIntegral.ringKrullDim_quotient_eq [Algebra.IsIntegral R S] (P : Ideal S) :
    ringKrullDim (S ⧸ P) = ringKrullDim (R ⧸ P.under R) :=
  have : FaithfulSMul (R ⧸ P.under R) (S ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  Algebra.IsIntegral.ringKrullDim_eq (R ⧸ P.under R) (S ⧸ P)
