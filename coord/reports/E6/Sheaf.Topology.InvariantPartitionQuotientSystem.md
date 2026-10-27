## What changed

Replaced the proof of `invariantPartition_quotient_system` in
`Sheaf.Topology.InvariantPartitionQuotientSystem`. Its signature, docstrings,
public imports and definitions are unchanged.

The indiscrete quotient gives nonemptiness, including when `P` is empty.
Intersection of invariant equivalence relations gives common refinements.
Mathlib's directed preorder instances then give cofilteredness of the opposite.
Mathlib's `DiscreteQuotient` API supplies finite discrete stages, continuous
surjective projections, and the refinement-map identities. Refinement maps are
surjective by lifting a coarse class to a point and projecting to the fine quotient.

The quotient action is constructed explicitly with `Quotient.map'`; its laws,
projection equivariance and refinement equivariance descend from representatives.
Applying the inverse group element proves equality of the translated fibers.
`continuous_prod_of_discrete_right` reduces continuity to each orbit map, which
is the continuous original orbit map followed by the quotient projection.
The final block criterion is projection equivariance after substituting the
chosen representative. No point of an empty space is assumed or chosen.

Searches through `msearch.py` (LeanFinder, Loogle and grep), and local searches
of Mathlib, WeilConjectures and Sheaf found the ordinary discrete quotient API
but no existing theorem providing the invariant system with its actions.

## Proved and sorry left

Closed: `invariantPartition_quotient_system`
(node `lem-sfb-invariant-partition-quotient-system`), the item's sole original hole.
Added: none. Remaining: none. Split off: none.

## No longer needed

None. Both existing imports are required by the unchanged statement.
The proof follows the existing node's common-refinement and quotient-action
argument, retaining both declared dependencies and the unit route. No module
or node is withdrawn; no additional proof imports are required.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The previously stated finite-partition
and continuity arguments can be implemented using Mathlib's existing discrete
quotient and discrete-factor continuity API without new intermediate results.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
