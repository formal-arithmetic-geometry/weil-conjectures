/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Quasi-finite over a polynomial algebra

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00QE
(blueprint: lem-weil-pbc-quasi-finite-over-polynomial-algebra).
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite type algebra is locally quasi-finite over a polynomial algebra in its fibre
 dimension.

Source: Stacks Project, Algebra, Lemma Tag 00QE
(blueprint: lem-weil-pbc-quasi-finite-over-polynomial-algebra).
Proof (the four steps of the node):

1. Put `p = q ∩ R`, `k = κ(p)` and `F = κ(p) ⊗[R] S`. The images of generators
of `S` generate `F` over `k` (lem-weil-pbc-quasi-finite-four-rings). The fibre-prime
bijection (lem-weil-pbc-fibre-ring-primes-bijection) supplies the point `Q` over `q`,
so `F` is nonzero. The definition of dimension at a point
(def-kun-topological-dimension-at-point) gives a neighbourhood `U` of `Q` of dimension
`n`. Choose a basic open inside `U` containing `Q`. By the localization-quotient
presentation (lem-weil-pbc-fibre-ring-localization-quotient), its defining element is
an image of `g₀ ∈ S` divided by a unit from `R ∖ p`. Thus it is `D(g₀)`, with
`g₀ ∉ q`. Its dimension is at most `n` by inclusion in `U` and at least `n` because
it is a neighbourhood of `Q`. Hence `T = κ(p) ⊗[R] S[g₀⁻¹]` has dimension `n`.

2. Noether normalization (lem-weil-pbc-noether-normalization-field) gives a finite
injective map `k[Y₁, …, Y_d] → T`; lem-zl-noether-normalization-dimension gives `d = n`.
Write each variable image as `sᵢ/g₀^eᵢ` divided by the image of `uᵢ ∈ R ∖ p`, using
lem-weil-pbc-fibre-ring-localization-quotient. Rescale each variable by the nonzero
scalar `uᵢ` in `k`. This is a polynomial-algebra automorphism and preserves the
subalgebra and finiteness. The rescaled images lift to `S[g₀⁻¹]`, defining an
`R`-algebra map `A = R[t₁, …, t_n] → S[g₀⁻¹]` whose base change to `k` is finite
(def-weil-pbc-mv-polynomial-ring).

3. Let `q₀` be the localized prime and `P` its contraction to `A`. Since `P ∩ R = p`,
the fibre `S[g₀⁻¹] ⊗[A] κ(P)` identifies with `T ⊗[k[t₁, …, t_n]] κ(P)` and is
finite-dimensional over `κ(P)`. It is Artinian
(lem-weil-pbc-finite-dim-algebra-artinian). Every prime is maximal, since its quotient
is a finite-dimensional domain over a field and hence a field. Its spectrum has
dimension zero and is discrete (lem-weil-pbc-finite-type-dim-zero-artinian). The
point over `q₀` is isolated, giving quasi-finiteness there
(def-weil-pbc-ring-map-quasi-finite-at-prime). The original generators together with
`g₀⁻¹` give finite type over `A` (def-weil-pbc-finite-type-algebra).

4. Openness of the quasi-finite locus (lem-weil-pbc-ring-quasi-finite-locus-open)
gives `h ∈ S[g₀⁻¹] ∖ q₀` such that the map to the further localization is
quasi-finite at every prime. Write `h = b/g₀^m`, with `b ∉ q`, and put `g = g₀*b ∉ q`.
The iterated localization is canonically `S[g⁻¹]`: both invert `g₀` and `b`
(def-weil-ring-localization-away). Transport the polynomial map across this
isomorphism. Its original generators and `g⁻¹` give finite type, and it is
quasi-finite at every prime, as required. -/
theorem exists_quasiFinite_over_polynomial_algebra
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (n : ℕ)
    (hdim : topologicalKrullDimAt
      (X := PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
      ((PrimeSpectrum.preimageHomeomorphFiber R S (q.comap (algebraMap R S)))
        ⟨q, rfl⟩) = (n : WithBot ℕ∞)) :
    ∃ (g : S) (hg : g ∉ q.asIdeal)
      (f : MvPolynomial (Fin n) R →ₐ[R] Localization.Away g)
      (hft : @Algebra.FiniteType (MvPolynomial (Fin n) R) (Localization.Away g)
        _ _ f.toRingHom.toAlgebra),
      ∀ (q' : PrimeSpectrum (Localization.Away g)),
        @Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) R) (Localization.Away g)
          _ _ f.toRingHom.toAlgebra hft q' := by
  sorry

end Algebra
