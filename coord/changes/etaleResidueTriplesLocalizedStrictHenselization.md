# etaleResidueTriplesLocalizedStrictHenselization

## Reason
Repair the equivalent-core reduction returned by the reviewer. Prove the core
by explicit localization and field constructions, a strictly smaller ring-cocone
comparison, and the existing local-base strict-henselization theorem.
No existing signature or definition changes.

## Old
The original item had a named sorry. The returned delivery proved it by a new
core with an equivalent conclusion, whose whole proof was a sorry.

## New
The original item is proved from the core and its structural-map calculation.
The core is now proved. The single remaining new theorem is
`AlgebraicGeometry.Scheme.etaleResidueTriples_primeLocalization_comparison`,
which compares ring colimits with already supplied algebra structures and has
no separable-closure or strict-henselization conclusion.
The new declarations are public in separate modules; imports used only by
proofs have no `public` modifier. All existing signatures remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization | P2 | proof import and item proof |
| Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselizationCore | P2 delivery | complete construction and comparison proof |
| Sheaf.RingTheory.EtaleResidueTriplesPrimeLocalizationComparison | P2 delivery | new strictly smaller ring-colimit comparison obligation |

## Status
landed 20261013T190151-L-3219893 2026-10-13 (merge of deliver/P2/Sheaf.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization)
