## What changed

Filled the only proof hole in
`lean/Sheaf/AlgebraicGeometry/SchemeEtaleCotangentRingMap.lean`:
`AlgebraicGeometry.Scheme.Hom.etaleDifferentialRingDirect_isRightAdjoint`.
The proof restricts the target of direct image to the affine étale basis of Y.
Its essential u-smallness makes the comma categories for pointwise left Kan extension
essentially u-small. Mathlib then supplies the left Kan extensions and ring sheafification
on X. The resulting direct image is the original functor followed by the affine
restriction equivalence; cancelling that equivalence proves the claim.

No imports were added: the existing imports already provide the required Mathlib API.
All declaration signatures, definition bodies, attributes and public imports are unchanged.
The shared node `lem-trf-space-enlarged-etale-ringed-site-model` gains a final proof step
recording this scheme-specific argument; its existing algebraic-space proof steps and
proof dependencies remain intact.

## Proved and sorry left

Closed 1 hole:
`AlgebraicGeometry.Scheme.Hom.etaleDifferentialRingDirect_isRightAdjoint`
(node `lem-trf-space-enlarged-etale-ringed-site-model`).
No holes added, no split-off statements, and no sorry remains in the item module.
The complete proof compiled in 5.8 seconds before the final style cleanup; delivery
rechecks the cleaned file and all its declarations with the generated axiom probe.
The proof uses Mathlib constructions rather than any sorried project theorem.

## No longer needed

None globally: no module, declaration, node or existing import is removed.
The four algebraic-space packages in this node's proof dependencies are unnecessary
for the scheme adjoint-existence clause proved here, but remain needed for its other
clauses. The existing public import `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`
continues to expose that existing interface, as recorded in the item's Lean attachment.
The proof needs no small model of X and no comparison to an algebraic-space ring inverse
image. The redundant trial proof import `Mathlib.CategoryTheory.Limits.EssentiallySmall` was
removed: it is already publicly available through the existing imports.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The existing proof docstring suggests passing to small skeletons
on both schemes. This can be shortened: only the affine basis on Y is needed. Its composite
with base change has small enough comma categories for Mathlib's Kan extension construction,
and cancellation of the affine restriction equivalence recovers the required adjunction.
No unit route or algebraic-space assertion is bypassed or changed. The proof is uniform for
identity maps, empty schemes and arbitrary morphisms; no finiteness or étaleness of f is
introduced.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
