## What changed

Kept the Sheaf compatibility module as a public re-export of the adopted,
fully proved `WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux`
implementation.  Clarified in the module documentation that this intentionally
provides one canonical declaration and avoids recreating the two derived tensor
pullback theorems.  No theorem declarations or upstream source files changed.

## Proved and sorry left

This is the assigned zero-hole synchronization repair.  The compatibility module
contains zero `sorry`s; the canonical declarations
`AlgebraicGeometry.RingedSpace.exists_tensorPullback_leftDerived` and
`AlgebraicGeometry.RingedSpace.leftDerived_tensorPullback_absolute` are fully
proved in the adopted source module.  Holes closed: zero.  Holes added: zero.

## No longer needed

The former duplicate Sheaf implementation and its direct proof imports are not
needed.  The canonical source module supplies the complete proofs and their
mathematical dependency closure.  No additional node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The current assignment is a listed zero-hole rework after upstream synchronization.
Reconstructing the old Sheaf implementation would recreate the duplicate declaration
collision; the correct repair is the canonical public compatibility import already
present on the branch.  The DAG attachments remain on the two canonical source
declarations and their statements are unchanged.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
