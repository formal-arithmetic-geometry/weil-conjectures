## What changed

Proved `rhsNormalization` in `lean/Sheaf/Paper/SystemFiniteRefinementMateRhsNormalization.lean`.
The proof uses `canonicalEvaluation`, a private categorical naturality cancellation lemma for
canonical push and shriek isomorphisms, and the new `rhsCore` transport statement. Added the
proof-only import of `Sheaf.Paper.SystemFiniteRefinementMateRhsCore`.

## Proved and sorry left

Closed the `rhsNormalization` sorry. Added one strictly smaller split-off theorem,
`rhsCore`, whose proof remains `sorry` in
`lean/Sheaf/Paper/SystemFiniteRefinementMateRhsCore.lean`; its DAG node is
`lem-sf-system-finite-refinement-mate-rhs-normalization-core`.

## No longer needed

No declared proof dependency was removed. The proof needs the canonical evaluation,
finite evaluation coordinates, and ambient proper/open calculus declarations; all remain
in the import closure.

## Where the brief, the DAG or earlier work was wrong

The original route omitted an explicit intermediate declaration for the finite evaluated
proper/open mate transport. That transport is strictly smaller than `rhsNormalization`
after the canonical bridge factors are cancelled, so it is recorded as `rhsCore`.

## New nodes

`lem-sf-system-finite-refinement-mate-rhs-normalization-core` is stated in
`lean/Sheaf/Paper/SystemFiniteRefinementMateRhsCore.lean`; its node is
`dag/nodes/sec-six-functors/lem-sf-system-finite-refinement-mate-rhs-normalization-core.json`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SystemFiniteRefinementMateRhsCore": "11143a2cc9e56fe267c0e08bbdc03a7bfd64079f", "Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization": "dcb576e232b2013dbc61c0a162693d68472bd2cd"}, "results": {"Sheaf.Paper.SystemFiniteRefinementMateCoordinates": {"hash": "1e7b21112c63fa53a9bc161c2eb0b537c411e35d", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T06:56:44+0800", "transitive": 0, "version": 1}
```

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
