/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Residue fields above a one-dimensional local domain

Source: Stacks Project, Algebra, Tag 031F, Lemma 10.119.10
(blueprint: lem-weil-pbc-dim-one-residue-field-extensions-finite).
-/

set_option autoImplicit false

universe uR uS uK uL

namespace Ideal

/-- Stacks Project, Tag 031F
(blueprint: lem-weil-pbc-dim-one-residue-field-extensions-finite).
For an injection of domains inducing a finite extension of fraction fields, with the base
Noetherian local of dimension one, primes above its maximal ideal are maximal, there are
finitely many, and their residue fields are finite extensions via the induced field map.

Proof: choose a nonzero element `x` of the maximal ideal. View `S` as an `R`-submodule of
`L`, and identify `L` with a finite direct sum of `K` using a basis. Apply
lem-weil-pbc-dim-one-submodule-quotient-finite-length to get finite length of `S/xS`.
The surjection onto `S/mS` preserves finite length: strict chains lift to strict chains.
Since the action factors through `R/m`, submodules are its vector subspaces, so this
closed fibre is finite dimensional. Apply lem-weil-pbc-finite-dim-algebra-artinian and
lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum to the fibre, then
lem-weil-pbc-spec-quotient-homeomorphism-zero-locus to identify its primes with the primes
above `m`. They are finitely many and maximal, including the case of the zero fibre.
Each quotient by such a prime is a quotient of the finite-dimensional fibre. Maximality
identifies it with the localization residue field, by sending a fraction to the quotient
of its numerator and denominator. This gives the finite residue extension. -/
theorem dim_one_residue_fields_finite
    (R : Type uR) (S : Type uS) (K : Type uK) (L : Type uL)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [FiniteDimensional K L]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (hcompat : ∀ r : R, algebraMap K L (algebraMap R K r) = algebraMap S L (φ r))
    (hdim : ringKrullDim R = 1) :
    (∀ n : PrimeSpectrum S,
      n.asIdeal.comap φ = IsLocalRing.maximalIdeal R → n.asIdeal.IsMaximal) ∧
    Set.Finite {n : PrimeSpectrum S | n.asIdeal.comap φ = IsLocalRing.maximalIdeal R} ∧
    (∀ (n : PrimeSpectrum S) (hn : n.asIdeal.comap φ = IsLocalRing.maximalIdeal R),
      letI := (Ideal.ResidueField.map (IsLocalRing.maximalIdeal R) n.asIdeal φ
        hn.symm).toAlgebra
      FiniteDimensional (IsLocalRing.maximalIdeal R).ResidueField n.asIdeal.ResidueField) := by
  sorry

end Ideal
