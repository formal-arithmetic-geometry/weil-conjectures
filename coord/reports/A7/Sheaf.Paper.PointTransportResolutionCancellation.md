## What changed

Filled `WeilConjectures.pointTransportResolutionCancellation` in
`Sheaf.Paper.PointTransportResolutionCancellation` without changing its signature.
The proof obtains the two quasi-isomorphism instances from exact sections and exact
inverse image, proves sigma naturality directly from the defining section formula,
and cancels the resolution and representative isomorphisms. Naturality of the
specified exact-functor localization comparison identifies the resulting chain map.
The normalized `sectionsRoos` comparison is retained throughout.
Scoped the heartbeat allowance to this theorem and disabled type-transparency
respect during elaboration to match the existing completed-coefficient APIs;
these are elaboration settings, with no change to the theorem's type.

Updated the node's proof step 2 and dependency list to record the direct section
argument. Removed its obsolete automorphism-naturality tool-use approval.

## Proved and sorry left

Closed: `WeilConjectures.pointTransportResolutionCancellation`
(node `lem-trf-point-transport-resolution-cancellation`), the item's one original hole.
Added: zero holes. Left in the item: zero holes. No split-off theorems.
This proves the item from the existing library declarations; it does not claim that
all the imported declarations are already free of sorry.

## No longer needed

Removed proof import `Sheaf.Paper.PointAutomorphismRestrictionNatural` and proof
node dependency `lem-weil-point-automorphism-restriction-natural`: the defining
`frobeniusPointIntegralSigma_existsUnique` formula and module-sheaf restriction
naturality prove the required strict square directly. No other nodes or modules
are withdrawn. The public statement prerequisites remain available to importers.

## Where the brief, the DAG or earlier work was wrong

The DAG's general automorphism-naturality theorem is stronger than needed for its
step 2. The local section calculation suffices, with no boundedness, completeness,
or constructibility condition. The unit route and all statements are unchanged.
The current blueprint unit was read under `literature/blueprint/latest/`; the
historical main-20261015 proof filename cited in the existing node is absent from
that current snapshot. No historical snapshot was substituted.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
