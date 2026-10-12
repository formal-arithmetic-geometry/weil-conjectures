/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Sheaf.RingTheory.ConormalModulePrincipalLocalization
import Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Sheaf.RingTheory.RegularSequenceConormal
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Stable conormal comparison with a complete intersection presentation

Source: Stacks Project, Algebra, proof of Lemma 00SC, last paragraph, using Lemma 00S6.
-/

@[expose] public section

universe u

namespace Ideal

/-- The local conormal module becomes finite free after adding the variables of a
complete intersection presentation of a principal localization.

Source: Stacks Project, Algebra, Lemma 00SC (lemma-lci), last paragraph of the proof,
through the equation from Lemma 00S6 (lemma-conormal-module-localize).
(blueprint: lem-weil-pbc-complete-intersection-presentation-stable-conormal)

Proof:
1. Put `S = k[x₁,...,xₙ]/I`, `Q = k[y₁,...,yₘ]`, and `J = (f₁,...,fₜ)`.
The prime `q` extends to a prime `p` of `S_g` because `g` is outside `q`.
The localization prime correspondence identifies `(S_g)_p` with `S_q`.
Pull `p` back through `e` and then through `Q → Q/J` to a prime `p'` of `Q`.
The algebra isomorphism `e` identifies the dimension of `Spec(Q/J)` with `m - t`.
The prime `p` proves `S_g` nonzero, hence `Q/J` is nonzero too. Since `t ≤ m`,
this dimension identity also reads `dim Spec(Q/J) + t = m`.
2. The global complete intersection local regular sequence theorem makes the images
of the `fᵢ` a regular sequence in `Q_{p'}`. The regular sequence conormal theorem
gives a basis of length `t` for `JQ_{p'}/(JQ_{p'})²` over `Q_{p'}/JQ_{p'}`.
3. Localization is exact: localize `0 → J² → J → J/J² → 0` at `Q ∖ p'`.
Localization of ideal products identifies `J²Q_{p'}` with `(JQ_{p'})²`, so the
localized conormal module is the conormal module in step 2. Localize the quotient
sequence too to identify its scalar ring with `(Q/J)_{e⁻¹(p)}`, hence with `S_q`.
The quotient action of `J/J²` and the fraction action on its localization agree
under these identifications. It follows that `(J/J²)_p` is `S_q`-linearly
isomorphic to `Fin t → S_q`.
4. Apply the principal localization conormal comparison to the quotient presentation
`k[x₁,...,xₙ] → S` and to `Q → Q/J → S_g`. Their kernels are `I` and `J`.
Localize the resulting isomorphism at `p`. Localization preserves finite products
and linear equivalences. The first summand identifies with `(I/I²)_q`: a fraction
`(x/gᵃ)/(s/gᵇ)` maps to `gᵇx/(gᵃs)`, and vanishing in either module means some
`gᶜs`, outside `q`, annihilates the numerator. Thus the fraction maps are inverse.
The scalar rings identify by step 1. Substitute the free module of step 3 and combine
the free factors of lengths `t` and `n` using `Fin (t + n) ≃ Fin t ⊕ Fin n`.
This yields the stated stable linear equivalence. No cancellation or local freeness
of `(I/I²)_q` is asserted here.
-/
theorem stable_conormal_of_completeIntersection_presentation
    {k : Type u} [Field k] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k))
    (q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))
    (g : MvPolynomial (Fin n) k ⧸ I) (hg : g ∉ q.asIdeal)
    (m t : ℕ) (f : Fin t → MvPolynomial (Fin m) k) (htm : t ≤ m)
    (e : (MvPolynomial (Fin m) k ⧸ Ideal.span (Set.range f)) ≃ₐ[k] Localization.Away g)
    (hdim : topologicalKrullDim (PrimeSpectrum (Localization.Away g)) =
      ((m - t : ℕ) : WithBot ℕ∞)) :
    Nonempty
      ((LocalizedModule q.asIdeal.primeCompl I.Cotangent ×
          (Fin m → Localization.AtPrime q.asIdeal)) ≃ₗ[Localization.AtPrime q.asIdeal]
        (Fin (t + n) → Localization.AtPrime q.asIdeal)) := by
  sorry

end Ideal
