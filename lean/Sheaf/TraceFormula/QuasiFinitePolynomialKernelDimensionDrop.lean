/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
import WeilConjectures.RingTheory.QuasiFiniteFourRings
import Sheaf.RingTheory.QuasiFiniteLocalDimension

/-!
# A nonzero polynomial relation lowers the dimension of a quasi-finite polynomial algebra

Source: Stacks Project, Algebra, Tag 00QK (lemma-finite-type-domain-over-valuation-ring-dim-fibres),
proof, final dimension inference (blueprint: lem-trf-quasi-finite-polynomial-kernel-dimension-drop).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- If a finite-type, everywhere quasi-finite algebra over affine `n`-space has a
nonzero polynomial relation, its spectrum has dimension strictly below `n`.
Blueprint: (blueprint: lem-trf-quasi-finite-polynomial-kernel-dimension-drop)
(Stacks Project, Algebra, Tag 00QK; blueprint:
lem-trf-quasi-finite-polynomial-kernel-dimension-drop.)

Proof (following the six steps of the node):
1. If `T` is the zero ring, its spectrum is empty and has bottom dimension. If `n = 0`,
   a nonzero element of the polynomial ring is a unit, so a kernel relation forces `T = 0`.
   Thus assume `T` is nonzero and `n ≥ 1`.
2. Put `P = k[t₁, …, tₙ]`. The field is Noetherian of dimension zero, so
   `lem-sf-noetherian-polynomial-dimension` gives `dim P = n`. Lexicographic leading
   exponents show that a product of nonzero polynomials is nonzero; hence `(0)` is prime.
3. Put `I = ker φ` and `R = P/I`, and define `ψ(p + I) = φ(p)`. This is well defined.
   Apply `lem-weil-pbc-quasi-finite-four-rings` to the square `(P, T, R, T)` with
   identity on `T`. Each `t = t * 1` verifies its finite-sum hypothesis, and a prime of
   the bottom `T` contracts to itself in the top `T`. Thus `ψ` is finite type and
   quasi-finite at every prime.
4. Choose nonzero `h ∈ I`. A strict prime chain of length `ℓ` in `R` lifts along the
   quotient surjection to a strict prime chain in `P`, all containing `h`. Prepending
   `(0)` gives length `ℓ + 1 ≤ n`. Thus all prime chains in `R` have length at most `n - 1`.
5. For a prime `q` of `T`, put `r = ψ⁻¹(q)`. By
   `lem-weil-pbc-localization-dimension-chains-below-prime`, `dim R_r ≤ n - 1`.
   Apply `lem-weil-pbc-dimension-inequality-quasi-finite` to `ψ` to obtain
   `dim T_q ≤ dim R_r ≤ n - 1`.
6. A prime chain of `T` ending at `q` has length at most `dim T_q` by the same
   localization chain formula. Taking the supremum gives `dim T ≤ n - 1 < n`.
   Finally `lem-weil-pbc-spec-topological-krull-dimension-ring` identifies this with
   the asserted topological dimension of `Spec T`.
(blueprint: lem-trf-quasi-finite-polynomial-kernel-dimension-drop.) -/
theorem topologicalKrullDim_spec_lt_of_quasiFinite_over_mvPolynomial_of_nonzero_kernel
    (k : Type u) [Field k] (n : ℕ) (T : Type v) [CommRing T] [Algebra k T]
    [Algebra.FiniteType k T] (φ : MvPolynomial (Fin n) k →ₐ[k] T)
    (hφ : @Algebra.FiniteType (MvPolynomial (Fin n) k) T _ _ φ.toRingHom.toAlgebra)
    (hq : ∀ q : PrimeSpectrum T,
      @Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) k) T _ _
        φ.toRingHom.toAlgebra hφ q)
    (hker : ∃ p : MvPolynomial (Fin n) k, p ≠ 0 ∧ φ p = 0) :
    topologicalKrullDim (Spec (CommRingCat.of T)) < (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
