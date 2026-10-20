## What changed

Retired the duplicate module `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`.
The sole consumer, `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`, now
imports `WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections`, the official
upstream twin. Its current proof is `sorry` and has no use of the old declaration, so
no theorem body or signature required adaptation. The withdrawn copy is listed in
`deleted.txt`. The DAG node `lem-pc-finite-affine-fibre-sections` now points to
`AlgebraicGeometry.Spec.exists_ringEquiv_stalk_tensorProduct_fiber` in the upstream
module. Change record: `coord/changes/retire-finite-affine-fibre-sections-20261020.md`.

## Proved and sorry left

This retirement closes no proof holes and adds no proof holes. The withdrawn Sheaf copy
had zero sorries before deletion. The adapted consumer retains its pre-existing
`sorry`, `AlgebraicGeometry.finiteLocallyFree_structureSheaf_properties`; it is outside
this retirement and its signature is unchanged.

## No longer needed

The duplicate module `lean/Sheaf/AlgebraicGeometry/FiniteAffineFibreSections.lean` is
withdrawn and listed in `deleted.txt`. No other imports, nodes, or modules are pruned.
The Sheaf theorem name `AlgebraicGeometry.finite_affine_fibre_sections` is no longer
needed; the DAG attachment uses the upstream theorem with its changed API.

## Where the brief, the DAG or earlier work was wrong

The previous E3 packet treated this item as a stale no-op after C8 had proved the Sheaf
copy. The current retirement queue instead requires migration to the official twin,
whose theorem is named `Spec.exists_ringEquiv_stalk_tensorProduct_fiber` and has a
`letI`-based API. The consumer currently has no completed proof call to rewrite, so the
import-only adaptation is sufficient.

## Forced adaptations

`Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf` is unclaimed. With the
withdrawn module absent, its original line 11 import fails because
`Sheaf.AlgebraicGeometry.FiniteAffineFibreSections` is unavailable. The required edit
replaces that one private import with
`WeilConjectures.AlgebraicGeometry.FiniteAffineFibreSections`. No declaration,
signature, proof body, or public import in the consumer changes. The adapted consumer
compiled successfully before delivery in 7.4 seconds. The sandbox-wide import-order
compile also passed. No newly introduced Sheaf/upstream twin pair occurs in its
import closure. The delivery dry run passed before this final metadata transcription
check; the final packet is checked again below by the delivery tool.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
