## What changed

Replaced the single sorry in `WeilConjectures.firstRootCoefficientScalarComparison`
by a construction from existing canonical integral-line and scalar-tower isomorphisms.
Only the assigned Lean module and its DAG proof record change. All added helpers
are private and proved; all added imports are proof imports. Existing public signatures,
definitions, imports and attributes are unchanged.

Generic private helpers package scalar extension of an isomorphism, the tower
isomorphism and transport along equality of coefficient maps. Their tensor
formulas are proved abstractly, avoiding unfolding the completed coefficient
rings during normalization.

The coefficient squares are checked using the actual finite quotient projections.
The normalization is proved on sheafification-unit tensor sections. Uniqueness uses
restriction to the discrete integer action, the existing integral forgetful
isomorphism and tensor/sheafification extensionality, so competing maps need not
be invertible and sections need not lift globally before sheafification.

## Proved and sorry left

Closed: `WeilConjectures.firstRootCoefficientScalarComparison`
(node `lem-pur-first-root-coefficient-scalar-comparison`): 1 of 1 original holes.
Added: 0 holes. Remaining in the delivered Lean module: 0.
No split-off theorems or modules.

Validation: the final file compiles without warnings through `lcompile.py` in
29.2 seconds. `#print axioms WeilConjectures.firstRootCoefficientScalarComparison`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Both added proof
imports pass the import-direction check. The original theorem signature and
DAG statement/Lean attachment are unchanged; only the node's proof, proof
dependencies and proof origin change.

## No longer needed

The assigned proof no longer directly needs node `lem-pur-twist-root-local-models`
or module `Sheaf.Paper.PurTwistRootLocalModels`: the already proved canonical
`integralExtensionReverse` isomorphism suffices, and the generic scalar-tower
isomorphism supplies invertibility. No imports were removed from the original
module; its public imports are retained. No module is withdrawn, and no claim
is made that the root local-model module is unused by other consumers.

## Where the brief, the DAG or earlier work was wrong

The planned primitive-root cover argument duplicates the canonical completed
integral comparison already proved privately in `PurTwistIntegralLocalModels`.
Importing that implementation with `import all` permits its reuse without
changing any shared module or adding a public API. The DAG proof now records
this shorter route. The theorem statement and unit route are unchanged.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FirstRootCoefficientScalarComparison": "45c2909745f97556f388ba110d9e1d38ab582266"}, "results": {"Sheaf.Paper.CoefficientTwistsDetailed": {"hash": "0deda6e116a7ea95d9063783cee229ea120737b8", "status": "OK"}}, "seconds": 95, "time": "2026-10-28T11:10:17+0800", "transitive": 0, "version": 1}
```

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
