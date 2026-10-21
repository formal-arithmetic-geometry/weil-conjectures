## What changed

Retired Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate in
favor of the existing, fully proved adopted-source twin with exactly the same
public declaration, AlgebraicGeometry.principalSubsetHorizontalFaceCoordinate.
The retained DAG node now points to the source module. Its mathematical statement,
proof plan, dependencies and unit route are unchanged. All upstream files remain
untouched. This completes the retirement assignment in coord/retire-items.tsv.

Validation through lcompile.py: the original item compiles unchanged (32.5 s);
a separate example with its full original signature is proved by the upstream
theorem (3.8 s), whose printed axioms are only propext, Classical.choice and
Quot.sound; the existing upstream HorizontalFaces parent compiles unchanged
(28.6 s). Searches used msearch.py leanfinder and loogle and local rg.

Change record: coord/changes/P4-retire-principal-open-cech-horizontal-face-coordinate.md.

## Proved and sorry left

Actual initial hole count: zero. Holes closed: zero. Holes added: zero. No sorry
is retained or split off. The retained source declaration
AlgebraicGeometry.principalSubsetHorizontalFaceCoordinate is already fully proved
without sorryAx. This is duplicate retirement, not a newly closed proof hole.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.PrincipalOpenCechSubsetHorizontalFaceCoordinate.
Its public import of WeilConjectures.AlgebraicGeometry.PrincipalOpenCechSubsetInsertion
and its private duplicate helpers disappear with the copy. No consumer imports
require removal: all current Lean and quarantine sources were checked, and the
parent already imports the upstream coordinate module. The former Sheaf parent
listed in the inventory is absent and its DAG record already points upstream.

No DAG node or mathematical dependency is pruned. In particular the coordinate
node is still needed by lem-sc-principal-open-cech-subset-horizontal-faces, and
both def-sc-principal-open-cech-subset-insertion and
def-sc-alternating-cech-total-complex remain necessary. The adopted-source theorem
and all its imports and proved dependencies remain intact.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a repeatedly split obligation, but the current
item already has a complete proof and coord/queue.tsv marks it retire. The concrete
work is the retirement assignment, not another decomposition. The old retirement
inventory lists one Sheaf.HorizontalFaces importer; current main has already
migrated this parent to the source library. The private-helper universe annotations
mentioned as API differences do not change the public theorem, as checked by the
full-signature Lean example. No mathematical statement is disputed.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
