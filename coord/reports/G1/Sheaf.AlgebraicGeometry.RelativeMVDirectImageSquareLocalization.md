## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RelativeMVDirectImageSquareLocalization.lean`
from its rework quarantine archive. Removed only `derivedPullback` from the local
`irreducible` attribute command: the current upstream declaration is already irreducible.
The source compiles through `lcompile.py` in 38.4 seconds with no diagnostics.
All theorem signatures, proof bodies, imports and existing blueprint tags are unchanged.
A dependency-ordered server compile also passed for the restored module (30.6 seconds)
and its unchanged archived direct consumer
`Sheaf.AlgebraicGeometry.RelativeMVNormalizedCoefficientRoof` (17.4 seconds).
The temporary consumer source was removed from the sandbox after this check; it is
not part of the delivery.
Change record: `coord/changes/relative-mv-square-localization-irreducible-rework.md`.

## Proved and sorry left

This is an assigned compilation repair, not a new proof or a decomposition.
Holes before: 0; holes closed: 0; holes added: 0; holes remaining: 0.
The existing complete theorem
`AlgebraicGeometry.relativeMV_direct_image_square_localization` is preserved,
as are the proved private helpers `square_paste`, `normalized_unit`,
`general_square_unit`, and `localization_unit_eq`.

## No longer needed

No imports, declarations, modules or mathematical dependencies are pruned.
Only the redundant local attribute entry for the already irreducible `derivedPullback`
is removed. The quarantined consumer and remaining rework cluster remain necessary.

## Where the brief, the DAG or earlier work was wrong

The upstream sync replaced the old derived-pullback implementation with an
`irreducible_def`. The archived module's attempt to set that declaration's local
reducibility status again now fails. Its mathematical proof needs no repair.
The rework archive contains zero `sorry` terms, as allowed for assigned repairs.
No current DAG node names this module or its archived blueprint tag
`lem-pc-relative-mv-direct-image-square-localization`; that pre-existing metadata
gap is recorded here without inventing a replacement proof dependency.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
