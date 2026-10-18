## What changed

Completed `AlgebraicGeometry.ProEtale.etaleOriginForgetfulPlus_essImage` in
`Sheaf.Paper.EtaleOriginDerivedCategory` using the direct argument already recorded
in its docstring. An essential-image representative supplies its retained etale
complex and comparison isomorphism; composing that isomorphism with the given
essential-image isomorphism constructs the required witness. Conversely, a witness
gives the induced-category object `(K, W)`, whose image is definitionally `K`.

The file compiled cleanly through `lcompile.py` in 3.7 seconds. Searches with
LeanFinder, Loogle and grep confirmed Mathlib's essential-image definition and
induced-category API; no additional import or intermediate theorem was needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.etaleOriginForgetfulPlus_essImage`
(node `def-sf-etale-origin-subcategory`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the item. No split-offs or other modules are added.

## No longer needed

None. No proof-dependency imports were present, and the recorded elementary route
is unchanged. No DAG nodes or modules are bypassed; existing public imports remain
the module's existing interface.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring's two-direction proof works directly. In particular,
the forward direction preserves the actual witness data and only composes its
comparison isomorphism; it does not choose data from an unproved existence claim.
The backward direction works for every supplied witness, without extra hypotheses
on the scheme, coefficient ring, or derived object.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
