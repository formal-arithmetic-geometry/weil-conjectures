## What changed

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.integral_normalized_ring_refinement_identity_core`
with its statement unchanged. Private proved helpers establish the identity coefficient
comparison, the sectionwise module pushforward identity laws, their inverse-image mates,
and their derived versions. Private versions of the existing identity mate calculations
for arbitrary universe levels reduce the specified proper/open word to inverse
cancellation.

The compatibility hypothesis `hg` forces the coefficient comparison along the identity
to be canonical; no additional global coherence on `Coefficients` is assumed. The
normalization hypothesis `hε` identifies the given open comparison with the inverse
canonical identity direct-image comparison. All constructed data are explicit, except
for the existing section-normalized composition isomorphism, whose existing uniqueness
theorem determines it.

Added proof imports of `Mathlib.CategoryTheory.Adjunction.CompositionIso`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`,
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus` and
`Sheaf.CategoryTheory.FlatScalarTowerCoherence`. The last two expose their proved
private generic helpers to this proof through `import all`.

Updated the item's DAG proof, proof dependencies and proof origin to this argument.
No other existing module or node is changed.

Validation: the final file compiled without warnings in 31.6 seconds.
`#print axioms` reported exactly `propext`, `Classical.choice` and `Quot.sound` in the
preceding diagnostic run; its profiling and axiom-print commands have been removed.
The unchanged direct importer
`Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent` compiled against this
core in 11.0 seconds. Its byte-identical temporary copy has been removed.

## Proved and sorry left

Closed the original one hole in
`WeilConjectures.ConstructibleExceptionalCoefficients.integral_normalized_ring_refinement_identity_core`
(node `lem-sf-integral-normalized-ring-refinement-identity-core`).

Added zero holes. No `sorry` remains in the delivered module. There are no split-off
statements; every private helper is proved. The proof uses existing stated library
declarations, notably `PurCompactSupport.modulePushComposition_existsUnique` and the
generic exact-derived unit and mate calculations.

## No longer needed

The planned dependency `lem-sf-integral-ringed-clopen-comparison`
(`Sheaf.SixFunctors.IntegralRingedClopenComparison`) is not needed for this identity calculation.
It suffices to compute the identity restriction directly from its defining counit and
the inverse-image unit law. No clopen comparison or invertibility theorem is used.

The construction package `Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData`
and the additional theorems of `Sheaf.Paper.RefinementOpenRestriction` are unnecessary
for the ambient statement and proof; the required definitions are in
`Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. The corresponding direct
imports are removed. Other consumers continue to need these modules. The unit's statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan suppressed the coefficient-identity normalization and both
module compositor unit calculations. These are necessary because `Coefficients` stores
arbitrary inverse-image identifications without global coherence. The existing `hg`
hypothesis supplies the needed identity coherence by cancellation, so the statement
requires no repair or extra hypothesis.

The existing private identity mate helpers fix the morphism universe one level below
the object universe. The ambient derived categories here have a different universe
shape. Private helpers reproduce the same proved generic argument with unrestricted
category universes, without changing any shared declaration. One exact-derived unit
calculation is also written with an explicit comparison isomorphism to avoid expensive
transport of the functor instances.

The cited exceptional-inverse-image definition does not itself display the claimed
identity diagram. The implemented argument uses the explicit section-normalized
compositors, the pro-étale site identity laws and the ordinary adjunction triangle laws,
which give the stated identity without that omitted diagram.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralNormalizedRingRefinementIdentityCore": "41d9b2197500c950c07b4fe40eaad3376889227b"}, "results": {"Sheaf.Paper.IntegralNormalizedRingRefinementIdentityComponent": {"hash": "b9205bf2f5c273d7f5a9121c4c66642404bb1df7", "status": "OK"}}, "seconds": 51, "time": "2026-10-28T10:45:46+0800", "transitive": 0, "version": 1}
```

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
