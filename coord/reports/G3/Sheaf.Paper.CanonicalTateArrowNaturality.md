## What changed

Added the named intermediate theorem `geometricTateCore` to split the six geometric,
coefficient, strict-system and root-tower clauses from the final parity conjunct. The
main theorem now combines that core theorem with a complete elementary proof using
`Int.negOnePow_eq_one_iff`; the original target signature is unchanged. Updated the
item DAG proof to record the split route and added the DAG node
`lem-pur-canonical-tate-arrow-naturality-core`.

The sandbox module compiles successfully with `lcompile.py`.

## Proved and sorry left

Closed `WeilConjectures.CanonicalTate.canonicalTateArrowNaturality` (1 of 1 original
sorries). The parity calculation is proved for all `r`, `s`, and integer `p`, including
zero exponents and `l = 2`.

Added one strictly simpler split-off hole:
`WeilConjectures.CanonicalTate.geometricTateCore`, recorded by node
`lem-pur-canonical-tate-arrow-naturality-core`. It contains exactly the six
non-arithmetic clauses needed by the target and is the next proof item.

## No longer needed

No imports or existing proof-dependency modules were removed. The parent proof route
now uses only the new core node and the elementary parity argument; its previously
listed detailed tool dependencies remain recorded as the dependencies of the core
argument.

## Where the brief, the DAG or earlier work was wrong

The original node presented the complete comparison argument and the even-shift parity
calculation as one monolithic theorem. No statement was mathematically changed; the
six-clause core is a strict decomposition that makes the remaining comparison proof a
separate named item. The target declaration and every existing definition are
unchanged.

## New nodes

`lem-pur-canonical-tate-arrow-naturality-core`: the six non-arithmetic clauses of the
canonical Tate laws, stated in `WeilConjectures.CanonicalTate.geometricTateCore` in the
item module. Its proof source and dependencies are recorded in the node JSON.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
