/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra
import Sheaf.RingTheory.QuasiFiniteFourRings

/-!
# Fibre dimension bound from a quasi-finite polynomial factorization

Source: Stacks Project, proof of Tag 00QH, after the application of Tag 00QE.
(blueprint: lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A quasi-finite factorization of `R → S[g⁻¹]` through a polynomial algebra in `n`
variables bounds the local dimensions of all the original fibres at primes in `D(g)`.
No distinguished prime or initial fibre-dimension hypothesis is needed.

Source: Stacks Project, Algebra, proof of Tag 00QH, the sentence "Considering the fibres",
using Tags 00PN, 00QG and 00E4.
(blueprint: lem-weil-pbc-fibre-dimension-bound-of-polynomial-factorization).

Proof: fix `q ∈ D(g)` and let `p` be its contraction to `R`. Localize `q` to a prime
`qg` of `S[g⁻¹]`; its contraction to `R` remains `p`. Write `k = κ(p)` and
`T = k ⊗[R] S[g⁻¹]`. Base change the given map to `k`. Polynomial scalar extension
identifies its source with `k[t₁, …, tₙ]`, and tensor cancellation identifies its target
with `T`. The four-rings theorem (Tag 00PN) makes this map finite type and quasi-finite
at every prime: the relevant tensor-product map is an isomorphism, hence surjective.
Also `T` is finite type over `k`, since the generators of `S` and `g⁻¹` generate it.
Tag 00QG bounds the global dimension of `Spec T` by `n`, so its local dimension at the
fibre prime corresponding to `qg` is at most `n` (local dimension is an infimum over
open neighbourhoods, including the whole space).

Localization commutes with base change, so `T` is the localization of `k ⊗[R] S` at
the image of `g`. Its spectrum is the principal open of that image. Under the fibre-prime
bijections the point for `qg` maps to the point for `q`: this follows by contraction,
since the bijection's inverse is contraction along the canonical tensor inclusion.
The latter point lies in this principal open because `g ∉ q`. The local dimension
at a point is invariant under an open-subspace inclusion. Thus the bound on `Spec T`
is exactly the asserted bound on the original fibre.

Edge cases: `n = 0` uses the same dimension bound; if `D(g)` is empty the conclusion is
vacuous. Neither injectivity of the polynomial map nor a domain hypothesis is needed. -/
theorem fibre_dimension_le_of_quasiFinite_polynomial_localization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [FiniteType R S] (g : S) (n : ℕ)
    (f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g)
    (hft : @FiniteType (MvPolynomial (Fin n) R) (Localization.Away g)
      _ _ f.toRingHom.toAlgebra)
    (hq : ∀ qg : PrimeSpectrum (Localization.Away g),
      @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) (Localization.Away g)
        _ _ f.toRingHom.toAlgebra hft qg)
    (q : PrimeSpectrum S) (hg : g ∉ q.asIdeal) :
    topologicalKrullDimAt
      (PrimeSpectrum.preimageEquivFiber R S (q.comap (algebraMap R S))
        ⟨q, rfl⟩) ≤ (n : WithBot ℕ∞) := by
  sorry

end Algebra
