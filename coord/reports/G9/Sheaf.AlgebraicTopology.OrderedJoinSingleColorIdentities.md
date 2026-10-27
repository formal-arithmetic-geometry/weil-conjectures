## What changed

Proved `AlgebraicTopology.OrderedJoin.singleColorIdentities` in
`Sheaf.AlgebraicTopology.OrderedJoinSingleColorIdentities` directly from the existing
face and linear-map constructions. Private proved helpers establish the face identities,
cardinalities, position-sign changes, and cancellation of the double-deletion sum.
The insertion calculation treats present and missing colors separately and then extends
both identities from the specified integer basis. The statement, definitions, public
imports, and existing docstrings are unchanged. The proof follows the existing DAG plan.

## Proved and sorry left

Closed the one original hole:
`AlgebraicTopology.OrderedJoin.singleColorIdentities`
(node `lem-sfb-ordered-join-single-color-identities`).
No holes remain in the item, no holes are added elsewhere, and no results are split off.
The proof uses no theorem from the imported module that contains `sorry`.
The final single-file compile passed without warnings (3.5 seconds).
`#print axioms AlgebraicTopology.OrderedJoin.singleColorIdentities` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. The existing import supplies the face and chain constructions used by the statement
and proof. No DAG dependency, unit step, module, or import is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The basis calculation works uniformly in integer
degrees, including the empty face, the top degree, and degrees with no symbols. It never
compares vertices, so it also covers coincident chosen and existing vertices. The
hypothesis `1 ≤ r` is retained verbatim although the calculation does not require it.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
