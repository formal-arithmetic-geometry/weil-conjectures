/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.RingTheory.HenselizationAtPrime
import WeilConjectures.RingTheory.FiniteRingMapQuasiFinite
import Sheaf.TraceFormula.HenselizationQuasiFiniteRing

/-!
# Ordinary henselization commutes with a local quotient

Source: Stacks Project, Algebra, Tag 05WQ, `lemma-quotient-henselization`
(blueprint: lem-trf-henselization-quotient-at-prime).
-/

@[expose] public section

universe u

namespace Algebra

/-- If `R` is local and `I` lies in its maximal ideal, quotienting an ordinary
henselization by the extended ideal gives an ordinary henselization of `R ⧸ I`.
The quotient map is local and surjective, the structural map from `R ⧸ I` is induced
from that of `R`, and the henselization structure of the quotient is the one whose
structural map from `(R ⧸ I)` localized at its maximal ideal extends this induced map.

Source: Stacks Project, Algebra, Tag 05WQ, `lemma-quotient-henselization`.
(blueprint: lem-trf-henselization-quotient-at-prime).

Proof. The quotient map `R → R ⧸ I` makes `R ⧸ I` a cyclic, hence finite, `R`-module,
so it is of finite type and quasi-finite at the maximal ideal `𝔪 / I`. Apply the
quasi-finite henselization comparison (Stacks Tag 05WP) with `A = R`, `B = R ⧸ I`,
`𝔭 = 𝔪` and `𝔮 = 𝔪 / I`: since both rings are local, their localizations at these
maximal primes are themselves, `Rʰ ⊗_R (R ⧸ I)` is `Rʰ / IRʰ`, and the prime generated
by `𝔮` is its maximal ideal, so the cited lemma identifies `Rʰ / IRʰ`, with the induced
structural map, with the henselization of `R ⧸ I`. The quotient map `Rʰ → Rʰ / IRʰ` is
surjective by construction; it is local because `R → Rʰ` is local, so `IRʰ` lies in the
maximal ideal of `Rʰ`. Since `I` maps to zero, the composite structural map
`R → Rʰ / IRʰ` factors uniquely through `R ⧸ I`, and the localization of `R ⧸ I` at its
maximal ideal maps compatibly.
-/
theorem henselization_quotient_at_prime
    (R : Type u) [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (H : Type u) [CommRing H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H]
    [HenselianLocalRing H]
    (hH : Algebra.IsHenselizationAtPrime R (IsLocalRing.maximalIdeal R) H) :
    ∃ (hJ : Ideal H),
      hJ = Ideal.map
          ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
            (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R)))) I ∧
      Function.Surjective (Ideal.Quotient.mk hJ) ∧
      IsLocalHom (Ideal.Quotient.mk hJ) ∧
      ∃ (aQI : Algebra (R ⧸ I) (H ⧸ hJ)),
        (algebraMap (R ⧸ I) (H ⧸ hJ)).comp (Ideal.Quotient.mk I) =
            (Ideal.Quotient.mk hJ).comp
              ((algebraMap (Localization.AtPrime (IsLocalRing.maximalIdeal R)) H).comp
                (algebraMap R (Localization.AtPrime (IsLocalRing.maximalIdeal R)))) ∧
        ∃ (hp : (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R)).IsPrime)
          (aH : Algebra (Localization.AtPrime
            (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R)))
            (H ⧸ hJ)),
          (algebraMap (Localization.AtPrime
              (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R))) (H ⧸ hJ)).comp
            (algebraMap (R ⧸ I) (Localization.AtPrime
              (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R)))) =
            algebraMap (R ⧸ I) (H ⧸ hJ) ∧
          ∃ (hQ : HenselianLocalRing (H ⧸ hJ)),
            @Algebra.IsHenselizationAtPrime (R ⧸ I) _
              (Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal R))
              (H ⧸ hJ) hp _ aH hQ := by
  sorry

end Algebra
