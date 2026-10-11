/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Étale at a prime and flat unramifiedness

Source: Stacks Project, Lemma 00U6 (lemma-characterize-etale),
lemma-unramified-at-prime, and Lemma 08WD
(blueprint: lem-sc-etale-at-prime-flat-unramified-criterion).
-/

@[expose] public section

namespace Algebra

universe u v

/-- For a finitely presented algebra, étaleness at `q` is equivalent both to an étale
basic neighbourhood and to flatness of `Rₚ → S_q` and vanishing of localized differentials,
where `p = q.under R` is the inverse image of `q`. The étale morphism
`Spec S_g → Spec R` of the node is the affine one, rendered as `Algebra.Etale R S_g`.
Source: Stacks Project, Tags 00U6 and 08WD, and lemma-unramified-at-prime.
(blueprint: lem-sc-etale-at-prime-flat-unramified-criterion)

Proof, following the node's four steps:
1. Apply `lem-sc-etale-at-prime-formally-etale-cotangent-criterion` to (1), obtaining
vanishing of localized H₁ and differentials. Finite presentation and
`lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing` give an étale basic open, so (2).
2. From (2), `lem-weil-pbc-etale-ring-map-iff-etale-affine` gives vanishing of H₁ and
of differentials on S_g. Localize at the prime induced by q, identifying its local ring
with S_q, and apply the localized cotangent criterion to obtain (1).
3. From (2), `lem-weil-pbc-etale-algebra-flat` gives flatness of S_g over R.
`lem-weil-pbc-flat-over-localization` gives flatness of S_q over S_g; transitivity
(Tag 00HC) gives flatness over R. Base localization gives flatness over Rₚ.
The affine étale criterion and localization of differentials (Tag 00RT) give (3).
4. From (3), `lem-weil-pbc-openness-of-flatness` gives g₁ outside q on whose basic open
all localizations are flat. `lem-weil-pbc-flat-over-localization` and
`lem-pc-affine-sections-flat-over-base` give flatness of S_{g₁} over R. Finite generation
of differentials gives g₂ outside q where they vanish. For g = g₁g₂,
`lem-weil-pbc-unramified-ring-map-iff-unramified-affine` gives unramifiedness.
Together with flatness and finite presentation, `def-weil-etale-morphism` gives (2). -/
theorem isEtaleAt_iff_exists_away_etale_iff_flat_localized_kaehler
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] :
    (IsEtaleAt R q ↔
      (∃ g : S, g ∉ q ∧ Algebra.Etale R (Localization.Away g))) ∧
    (IsEtaleAt R q ↔
      (RingHom.Flat
          (Localization.localRingHom (q.under R) q (algebraMap R S) rfl) ∧
        Subsingleton (LocalizedModule q.primeCompl (KaehlerDifferential R S)))) := by sorry

end Algebra
