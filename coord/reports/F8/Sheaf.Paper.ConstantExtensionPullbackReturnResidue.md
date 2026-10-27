## What changed

Filled `constantExtensionPullbackReturn` using `constantExtensionWeilHeartEquivalence`,
choosing a field isomorphism from the given algebraic closure to `ℂ` via
`IsAlgClosure.equiv` and `PadicAlgCl.nonempty_ringEquiv_complex`. The existing equivalence
supplies the restriction specification, finite-limit and finite-colimit preservation, and
the inverse comparison. Added the strictly smaller named theorem
`constantExtensionRestriction_normalization` for the remaining cyclic-coordinate
normalization, with its DAG node; its proof is left for a follow-up worker.

## Proved and sorry left

Closed the `constantExtensionPullbackReturn` sorry. One sorry remains, in
`constantExtensionRestriction_normalization` (node
`lem-zl-constant-extension-pullback-normalization`), which is the componentwise cyclic
normalization needed to combine the sheet-coordinate equivalence with the restriction
specification.

## No longer needed

None. The existing imports and the equivalence dependency are used. The added Padic-to-
complex theorem import is used only to instantiate the existing equivalence theorem.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the full cyclic normalization as if it were already a
consequence of the restriction specification. The available equivalence theorem proves
the restriction specification and exactness, but the all-coordinate normalization is a
separate step. It is therefore split into the new strictly smaller node above.

## New nodes

`lem-zl-constant-extension-pullback-normalization` records the all-coordinate cyclic
normalization for the functor selected by the existing constant-extension equivalence.
The declaration is in the item module and is the sole remaining sorry.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
