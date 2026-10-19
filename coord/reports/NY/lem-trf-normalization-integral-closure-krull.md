## Worker report

The module `Sheaf.RingTheory.NormalizationIntegralClosureKrull` states
`RingTheory.normalization_integralClosure_isKrull`. It introduces the canonical
localization-to-fraction-ring map `normalizationLocalizationMap` using
`IsLocalization.map`, and the subtype `normalizationHeightOneIndex` of nonzero
height-one prime ideals. The theorem states the Mori–Nagata result for
`integralClosure R (FractionRing R)`.

The hypothesis `(R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]`
renders the commutative Noetherian integral domain hypothesis. The existential
witness `hN : IsDomain (integralClosure R (FractionRing R))` renders that the
normalization is a domain. The first conjunct quantifies a prime `P`, its prime
instance, nonzeroness, and the condition that every strictly smaller prime is
bottom; this is exactly a nonzero height-one prime. It gives the three requested
properties of `AtPrime P`: `IsNoetherianRing`, `IsDomain`, and
`IsIntegrallyClosed`, i.e. a Noetherian normal domain. The second conjunct is
the intersection clause, represented inside `FractionRing` of the normalization
by equality of the image of its algebra map and the intersection of the images of
the canonical maps from all height-one localizations. The final conjunct says
that for every nonzero normalization element, the set of nonzero height-one
primes containing it is finite. The subtype is empty when there are no
height-one primes; the intersection then has the usual empty-intersection
interpretation supplied by `Set.iInter`.

Dependencies used: `IsNoetherianRing` from
`Mathlib.RingTheory.Noetherian.Defs`; `integralClosure` from
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`; `Localization.AtPrime`
from `Mathlib.RingTheory.Localization.AtPrime.Basic`; and
`IsIntegrallyClosed` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`.
The fraction field is Mathlib's `FractionRing`. The dependency node
`def-weil-pbc-normal-ring` records the inline normal-domain form
`IsDomain A ∧ IsIntegrallyClosed A`; the theorem uses those exact two
predicates on each localization.

Edge cases checked: the height-one subtype can be empty; the empty indexed
intersection is therefore present. The theorem permits the zero ring only when
consistent with the explicit `IsDomain` hypothesis, whose `Nontrivial` field
excludes it. The finite-character clause explicitly excludes `x = 0`, as in the
source. Prime localization uses the recorded prime instance and does not add a
Noetherian or dimension hypothesis.

Searches made: `msearch.py ... leanfinder "Mori Nagata theorem the integral
closure of a Noetherian integral domain in its own fraction field is a Krull
domain"` returned only Dedekind and integral-closure Noetherianity results;
`loogle "integralClosure KrullDomain"` returned no hits and reported
`KrullDomain` unknown; `msearch.py ... grep "Mori|Nagata|KrullDomain|isKrull"
RingTheory` returned only Morita and Krull-dimension occurrences. LeanSearch
queries for “normalization of a Noetherian domain is Krull” likewise returned
only Dedekind/Krull-dimension results. `rg` over the source and project found
no Mori–Nagata or Krull-domain declaration (the only project hit was a proof
comment referring to this node). Thus no existing declaration matched.

The theorem proof is `sorry` as required for stage 2; no mathematical claim is
proved in this delivery.

## Second reading by NY

I reread the node and module independently. The ring, domain, and Noetherian
hypotheses are all explicit. The normalization is Mathlib's canonical
`integralClosure`, and the height-one condition is rendered as nonzero plus no
prime strictly between bottom and the given prime. Clause (i) has all three
parts, clause (ii) compares the normalization image with the complete
height-one localization intersection in its fraction field, and clause (iii)
quantifies finiteness for each nonzero element. The localization map is
canonical and uses no arbitrary choice. No mismatch or omitted edge case was
found.
