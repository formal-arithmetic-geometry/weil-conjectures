## What changed

Proved `AlgebraicGeometry.Etale.SfP1Transport.diagonalSection_forgetSupports` in
`Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports` from the existing
`diagonalSection_forgetSupports_unit`. A proved private categorical lemma postcomposes the
identity-coefficient equality with the direct image of an arbitrary coefficient map, then
uses naturality and functoriality. Private proof-building helpers construct ordinary
kernel-checked congruence proofs, following the existing
`OrdinaryFiniteDiagonalChartExchangeAux` method. They compare proposition arguments by
proof irrelevance and keep derived localization constructions folded.

The public theorem statement, docstring, imports, and shared definitions are unchanged.
The node proof now records the implemented categorical calculation. The unit route and
its sole mathematical proof dependency are unchanged. No other module is delivered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.SfP1Transport.diagonalSection_forgetSupports`
(node `lem-sf-diagonal-section-forget-supports`). Its private categorical helper
`coefficient_naturality` is also proved. The item has zero remaining `sorry` occurrences.
Holes added: 0. Statements split off: 0.

The imported `diagonalSection_forgetSupports_unit`
(node `lem-sf-diagonal-section-forget-supports-unit`) is an existing open dependency;
its source, statement, proof and node are untouched. This delivery proves the requested
naturality step from that declared dependency, rather than claiming to close its
compactification-normalization obligation.

## No longer needed

None. No imports, nodes or modules were removed. The existing unit normalization is the
only project theorem used in the proof; both public imports supply statement definitions.

## Where the brief, the DAG or earlier work was wrong

The stated reduction is valid, and no mathematical statement needed correction. The
previous delivery left both the general theorem and its coefficient-free special case
open. The general theorem now follows from that special case by a complete Lean proof.

Direct concrete rewriting and direct application of the generic lemma exceeded the
kernel-checking budget, although the unchanged statement compiled in 6.2 seconds.
Explicit structural congruence at the two specialization boundaries removes the expensive
comparison of separately elaborated category-instance witnesses. The resulting complete
proof compiled in 8.4 seconds with a temporary lower diagnostic heartbeat limit; that
option was removed before final validation. The construction is unchanged for empty
schemes, the zero coefficient ring, both Boolean projections and zero coefficient maps.
No shared definition, resource limit or kernel check was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.SfDiagonalSectionForgetSupports": "9761fec81a26b17d3d4ded7fc4c4678ef38fc72a"}, "results": {"Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison": {"hash": "4d112be67e7bb62260edbac89d1f7fc5009fa980", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T10:35:18+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
