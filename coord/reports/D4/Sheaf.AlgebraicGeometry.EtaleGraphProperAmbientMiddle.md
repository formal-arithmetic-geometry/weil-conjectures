## What changed

Proved `AlgebraicGeometry.Etale.etaleGraphProperAmbientMiddle` in
`Sheaf.AlgebraicGeometry.EtaleGraphProperAmbientMiddle`. Its statement and public
import are unchanged. Added one proof-only import,
`Sheaf.AlgebraicGeometry.SfExactExchangePasting`, and fully proved private helpers.
No other Lean module or existing definition is changed.

The proof constructs the map of the two intersections and proves that both
projection squares are Cartesian. Horizontal and vertical exchange pasting in
the exact unbounded formalism give naturality of each forward intersection leg.
The specified middle comparison is the inverse first leg followed by the second;
the common intersection transport then cancels. The private normalization lemmas
identify the formalism's identity, open exchange and proper compositor with the
concrete derived-category maps occurring in the statement.

Updated the existing node's proof, proof dependencies and proof origin to record
this Cartesian argument. The blueprint unit route is preserved.

Validation: server compilation through `lcompile.py` and the required delivery
preflight. The complete proof compiles in approximately 18 seconds. Final
cleanup removed the fallback tactic that Lean reported as unreachable after
simplification closed the last goal.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Etale.etaleGraphProperAmbientMiddle`
(node `lem-pur-etale-graph-proper-ambient-middle`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the item: 0.
Every private helper is proved; no split-off statement or new module is added.

## No longer needed

The old planned direct proof dependencies
`lem-pur-etale-proper-open-exchange-cube`,
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, and
`lem-cbc-extension-zero-composition` are not needed as separate inputs to
this proof. All squares here are Cartesian, so the proved horizontal and vertical
mate-pasting laws, with the exact unbounded normalization, suffice. The first of
these is a general non-Cartesian exchange cube; no such comparison family is
needed here. The concrete proper and open compositors are obtained from the
already proved exact formalism.

No existing public import is removed. No module is withdrawn or claimed to be
pruned from the whole target closure: the omitted dependencies may still be used
elsewhere. The proof uses only the added exact-exchange proof import, rather than
the broader unbounded-comparison or general-cube modules explored during drafting.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The planned general cube was
more general than required for this Cartesian intersection grid. The two previous
splits can be closed here without another postponed obligation. No target
statement, public definition, source-library declaration or unit route is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
