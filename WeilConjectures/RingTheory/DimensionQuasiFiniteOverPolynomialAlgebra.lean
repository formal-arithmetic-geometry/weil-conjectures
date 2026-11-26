/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import Mathlib.RingTheory.KrullDimension.Polynomial
import WeilConjectures.RingTheory.QuasiFiniteLocalDimension
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Dimension of a quasi-finite algebra over affine space

## Implementation details

For a prime `q` of `T` over `p` in the polynomial ring `P`, the local dimension inequality for
quasi-finite maps bounds `dim T_q` by `dim P_p ≤ dim P = n`. The spectrum dimension equals the
ring dimension, which is bounded via `ringKrullDim_le_iff_height_le`; this includes the empty
spectrum, so no nontriviality assumption on `T` is needed.

## References

* [Stacks, Tag 00QG]
* [Stacks, Tag 00QF]
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- A finite-type `k`-algebra with a quasi-finite `k`-algebra map from the polynomial
ring in `n` variables has spectrum of dimension at most `n`. -/
theorem topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial
    (k : Type u) [Field k] (n : ℕ) (T : Type v) [CommRing T] [Algebra k T]
    [Algebra.FiniteType k T] (φ : MvPolynomial (Fin n) k →ₐ[k] T)
    (hφ : letI := φ.toRingHom.toAlgebra
      Algebra.FiniteType (MvPolynomial (Fin n) k) T)
    (hq : letI := φ.toRingHom.toAlgebra
      letI : Algebra.FiniteType (MvPolynomial (Fin n) k) T := hφ
      ∀ q : PrimeSpectrum T, Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) k) T q) :
    topologicalKrullDim (Spec (CommRingCat.of T)) ≤ (n : WithBot ℕ∞) := by
  let := φ.toRingHom.toAlgebra
  let : Algebra.FiniteType (MvPolynomial (Fin n) k) T := hφ
  change topologicalKrullDim (PrimeSpectrum T) ≤ (n : WithBot ℕ∞)
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro q hqprime
  let := hqprime
  let Q : PrimeSpectrum T := ⟨q, hqprime⟩
  have hlocal := Algebra.ringKrullDim_le_of_isQuasiFiniteAtPrime
    (MvPolynomial (Fin n) k) T Q (hq Q)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q.asIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height
      (Q.comap (algebraMap (MvPolynomial (Fin n) k) T)).asIdeal] at hlocal
  have hsource :=
    (Q.comap (algebraMap (MvPolynomial (Fin n) k) T)).asIdeal.height_le_ringKrullDim_of_isPrime
  have hdim : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance]
    simp
  exact hlocal.trans (hsource.trans hdim.le)

end AlgebraicGeometry
