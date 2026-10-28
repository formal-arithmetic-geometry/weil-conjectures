## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_trace_equation` in
`Sheaf.Paper.ScalarTraceEquation` directly from the existing exchange definition.
The right-hand side of `ScalarTraceWitness.exchange_eq` now uses
`secondPretraceExchangeMap`, the existing fixed-endpoint wrapper whose body is
exactly the native exchange component previously written there. Unfolding
`secondTraceExchange` now makes the equality reflexive without expanding the
native derived constructions at a specialized rational coefficient ring.

The field's mathematical content is preserved by definitional equality; the
theorem's signature is unchanged. No new declaration or import is added.
The representation change and all consumers are recorded in
`coord/changes/scalar-trace-equation-node.md`.

Corrected the node's natural-language statement to its actual Lean witness and
replaced its placeholder proof by this defining-equality argument. Both parent
nodes remain valid, as recorded in `statement_change`.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.RationalP1.scalar_trace_equation`
(node `lem-sfb-scalar-trace-equation`). Added 0 holes and split off 0 statements.
The delivered module has no `sorry`. Its proof constructs the existing witness
and unfolds the existing `secondTraceExchange` definition. Single-file validation
passed in 7.5 seconds, with no warnings. An ordered three-file check then
compiled the delivered module in 9.2 seconds, unchanged
`Sheaf.Paper.ScalarComponentFromTrace` in 14.8 seconds, and unchanged
`Sheaf.Paper.ScalarP1UnitMateComponent` in 11.6 seconds against it. Temporary
consumer source copies were removed after checking; they are not delivered.

## No longer needed

No imports, modules, or nodes are pruned. Both public imports provide the
statement and its existing instance setup; the private `import all` supplies
the existing local pullback shift instance. No proof-dependency import is added.

The unshifted line-composition calculation described by the old node prose is
not needed to prove this witness. Its separate node
`lem-sfb-rational-tate-line-comparison-composition` remains used elsewhere in
the parent route and is not withdrawn. There were no old proof dependencies
to remove.

## Where the brief, the DAG or earlier work was wrong

The assigned hole is the defining second-trace exchange equality. Expanding
the native component at the rational line is prohibitively expensive: the
direct proof elaborated but hit a kernel timeout at 116 seconds, and the
profiled arbitrary-coefficient helper attempt exceeded 120 seconds. Folding
the witness's native component through its already existing fixed-endpoint
wrapper removes that repeated conversion while preserving the equality.
No definition or instance contains a new hole.

The original node prose and title instead described composition of unshifted
Tate-line maps; its proof was a placeholder with no argument. The corrected
statement records the old text and both citers, whose Lean uses already agree
with this witness. Maintainer-owned title and source fields are left for the
maintainer to reconcile; accurate sources are in `proof_origin` and
`statement_change`.

The unit's projective-line adjunction route is preserved. Finite coefficient
indices, the algebraic-closure index, and arbitrary Y are covered uniformly
because the maps are identical by construction. There is no added hypothesis.
Current server records identify a one-hole proof item, with no rework,
build-error, or F7 return entry.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.ScalarTraceEquation": "72428f3868cc6e7ab4e3d4c2cb6ebc75b06c579e"}, "results": {"Sheaf.Paper.ScalarComponentFromTrace": {"hash": "2f717160f5d3cd72ff942a9789a9a1682ead6618", "status": "OK"}, "Sheaf.Paper.ScalarP1UnitMateComponent": {"hash": "532c89db1d2eb27a104d3e7c6cbf9d173fdcbc7d", "status": "INFRA"}}, "seconds": 131, "time": "2026-10-28T10:24:49+0800", "transitive": 0, "version": 1}
```

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
