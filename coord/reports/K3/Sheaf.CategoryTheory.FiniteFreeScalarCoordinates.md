## What changed

Proved `CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates` in
`Sheaf.CategoryTheory.FiniteFreeScalarCoordinates`, preserving its signature, the predicate,
and every public import. Added the private proof import
`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal` (import-cycle check passed).
All new helpers are private and proved.

The proof first identifies restricted scalar extension with the existing relative tensor
of the restricted regular B-module and M, using the canonical coequalizer projections.
Tensoring the chosen basis isomorphism, distributing over its finite biproduct, and applying
the relative left unitors gives the finite-product isomorphism. The two specified morphism
formulas follow from the projection identities and explicit relative-unit formulas.
Naturality is checked after the coequalizer projection and each product projection.
The canonical sheaf tensor properties supply all packaged infrastructure.

Updated the item's DAG proof and dependencies to describe this categorical implementation,
including the already-existing `def-sfb-modobj-relative-tensor` declaration. It is the same
finite-free argument in the final sentence of the cited blueprint proof; no unit step is
bypassed. No source-library file or public interface was changed. The record
`coord/changes/finite-free-scalar-coordinates-private-section.md` documents the local helper
section and variable commands that the conservative static interface check flagged. The
downstream tool reports zero consumers and both public names occur only in the item itself;
the unfinished DAG parent keeps the same statement and needs no adaptation.

Validation: the complete module compiled cleanly through lcompile.py in 5.6 seconds;
a final axiom probe compiled cleanly in 5.7 seconds and reported exactly `propext`,
`Classical.choice`, and `Quot.sound` for the theorem (no transitive sorry).
The construction works for arbitrary n, including n = 0: finite biproduct distributivity
and the empty inverse sum require no nonzero or positive-rank assumption. Zero rings and
zero modules also require no additional hypotheses.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Mod.sheaf_finiteFreeScalarCoordinates`
(node `lem-sfb-finite-free-scalar-coordinates`).

Proved 1 of 1 original sorries. Added 0 holes; split off 0 statements.
No sorry remains anywhere in this delivery.

## No longer needed

None: no imports, nodes, modules, or declarations were removed. All three original
dependencies are still used. The elementwise inverse calculations are implemented by the
existing relative tensor and Mathlib finite-biproduct isomorphisms, whose inverse identities
already perform those calculations; no extra sectionwise tensor theory is needed.

Searches through msearch.py (leanfinder, loogle and grep), the adopted library and Mathlib
found the existing internal relative tensor and Mathlib rightDistributor. No existing
finite-free scalar-coordinate theorem was found. These constructions give the complete
proof without new public statements.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's local tensor formulas are valid; the existing
relative-tensor API realizes them directly by universal properties and avoids expanding
sheaf sections. The original proof omitted this reusable categorical implementation.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
