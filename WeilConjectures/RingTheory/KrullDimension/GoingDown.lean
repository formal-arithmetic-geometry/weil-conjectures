/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Going down and surjective spectra bound Krull dimension

If a ring map has going down and is surjective on prime spectra, then the Krull dimension of
the source is at most that of the target.

## Implementation details

A strict chain `p₀ < ⋯ < pₙ` in `R` is lifted to `S` by choosing `qₙ` over `pₙ` and applying
going down successively; the lifted inclusions are strict since contractions differ.

## References

* [Stacks, Tag 00OH]
* [Stacks, Tag 00HV] (going down)
-/

@[expose] public section

universe u v

/--
Going down together with surjectivity on prime spectra implies the Krull-dimension
inequality. The going-down property of `φ` is Mathlib's `Algebra.HasGoingDown` for the algebra
structure `φ.toAlgebra`.
-/
theorem ringKrullDim_le_of_goingDown_of_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (hgoing : letI := φ.toAlgebra; Algebra.HasGoingDown R S)
    (hsurjective : Function.Surjective (PrimeSpectrum.comap φ)) :
    ringKrullDim R ≤ ringKrullDim S := by
  let := φ.toAlgebra
  have : Algebra.HasGoingDown R S := hgoing
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨Q, hQ⟩ := hsurjective l.last
  have : Q.asIdeal.LiesOver l.last.asIdeal := by
    constructor
    exact (congrArg PrimeSpectrum.asIdeal hQ).symm
  obtain ⟨L, hlength, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  exact hlength ▸ Order.LTSeries.length_le_krullDim L
