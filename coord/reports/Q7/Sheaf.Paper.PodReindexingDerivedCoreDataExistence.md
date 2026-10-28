## What changed

Proved `WeilConjectures.podReindexingDerivedCoreData_exists` in
`Sheaf.Paper.PodReindexingDerivedCoreDataExistence`, preserving its complete signature.
Its proof, private proof imports, and one proved private functoriality helper change. The associated node's proof,
proof dependencies and proof origin now describe the Lean construction.

The private `coreComplexTowerSquare` helper performs the complex/tower interchange
for abstract additive functors, avoiding expansion of concrete sheaf constructions.
The two fixed completion models give normalized Roos models. The ordinary
restriction square descends to derived restriction, and its adjoint square gives
finite scalar extension. The canonical ordinary evaluation comparison descends
after identifying finite geometric pullback with sectionwise inverse image by
uniqueness of left adjoints. The given strict natural Roos comparison, together
with the whole restricted-tower inverse-image unit, gives a natural comparison
on all system complexes. Localization descends it to the derived limit square.
Its adjoint square gives reduction. Finally the existing primitive quotient
pullback model supplies the pullback realization, completing all eight fields.

The complete proof compiled on the server in 21.7 seconds. Final delivery checks
also validate the warning cleanup and the proof packet.

The construction does not use finite evaluations to detect derived morphisms.
It works in the original independent site and coefficient universes and does
not impose additional restrictions on the schemes, complexes or towers.

## Proved and sorry left

Closed the one hole in `WeilConjectures.podReindexingDerivedCoreData_exists`
(node `lem-pod-reindexing-derived-core-data-existence`).
Original holes: 1. Remaining holes in the item: 0. Added holes: 0.
No split-off statements or modules were added.

## No longer needed

No original imports were removed. Every added import is used by the proof.
The original planned dependency `lem-cbc-exact-product-functor-strict-limit`
(`Sheaf.Paper.ExactProductFunctorStrictLimit`) is unnecessary here: the supplied
natural strict Roos isomorphism and normalized Roos models directly descend to
the required derived limit isomorphism.

The aggregate `lem-trf-primitive-quotient-realization-comparisons`
(`Sheaf.Paper.PrimitiveQuotientRealizationComparisons`) is not imported. Its
specific pullback component, already stated and proved as
`lem-trf-primitive-quotient-pullback-model-existence`, suffices. This does not
assert that either module is globally unreachable or withdraw any module.

The nonexistent proof dependency `lem-pod-reindexing-derived-core-data` was
corrected to the actual record node `def-pod-reindexing-derived-core-data`.
The strict comparison and coefficient evaluation calculus dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The old proof plan was too broad: raw maps can be assembled using existing
exact-functor descent, normalized Roos models and adjunction uniqueness. No
additional version of the raw existence statement is needed. The node also
misspelled the raw record node's `def-` prefix as `lem-`; its proof dependency
and step references are corrected.

This delivery establishes raw comparison data only, as the statement requests.
The five downstream normalization-law statements are not used or proved here.
No existing definitions, statement signatures, public imports or other modules changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingDerivedCoreDataExistence": "8c1f3279c31e0616cd1685d33f90cfe6a632ebf6"}, "results": {"Sheaf.Paper.PodReindexingDerivedComparisonsCore": {"hash": "17a9f282d9d87372fb63f9628de9885184021152", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:34:08+0800", "transitive": 0, "version": 1}
```

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
