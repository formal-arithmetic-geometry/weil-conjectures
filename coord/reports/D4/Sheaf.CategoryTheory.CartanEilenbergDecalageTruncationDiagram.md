## What changed

Restored `lean/Sheaf/CategoryTheory/CartanEilenbergDecalageTruncationDiagram.lean`
from the quarantine path recorded in `coord/rework.tsv` (cluster-restore rework).
The full archived implementation is retained, including the public theorem
`CategoryTheory.cartanEilenberg_decalage_truncation_diagram`, both proved private helpers,
and all original public and proof imports. This repairs the missing source module;
it is not a withdrawal or a replacement by an empty module.

The comparison isomorphisms are constructed explicitly from the compatible full/cut
injective models, the derived unit, localization homology, and the prescribed resolution
comparison. Naturality proves the inclusion square. Cancelling the localization of the
full augmentation and applying the resolution-unit identity proves normalization.

Read both declared dependency statements and verified that the restored proof uses
`cartanEilenberg_decalage_injective_model` and
`exists_grothendieck_resolution_unit_comparison` exactly as the node plans. Searched
Mathlib and both library roots for a shorter comparison; no replacement for this
paired square and normalization was found. The item's existing node and Lean attachment
remain correct, and the unit record has no realized step affected by this restoration.

Validation: the restored module compiled through `lcompile.py` in 6.9 seconds, with
no errors or warnings. All existing signatures, definitions, docstrings and visibility
are identical to the quarantine archive. No consumer adaptation is needed.

## Proved and sorry left

The restored theorem `CategoryTheory.cartanEilenberg_decalage_truncation_diagram`
(blueprint `lem-sp-ce-decalage-truncation-diagram`) has a complete Lean proof of both
conclusions. The private `unitHomologyMap_naturality` is proved and `unitHomologyIso`
is an explicit isomorphism construction, with no postponed data.

Actual local hole count in the archive: zero. Actual local hole count delivered: zero.
Holes closed in this repair: zero; holes added: zero; split off: zero.
No declaration in this packet is left with `sorry`. This is restoration of an already
proved quarantined module, not a claim to have newly closed its hole or the dependencies'
transitive holes.

## No longer needed

None. Both existing proof dependencies remain needed. No imports, modules, declarations,
DAG attachments or proof steps are removed or bypassed. In particular the quarantined
parent `Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation` still imports and
applies this theorem; its node still lists this dependency. The archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes; the current rework assignment is
instead the missing-source restoration recorded after a cluster restore. The quarantine
source already has zero local holes and compiles against the current library unchanged.
No mathematical statement repair, definition repair, new node, or new proof split is needed.
The source-only downstream script reports the missing module as unknown, so the consumer
check also searched the quarantine tree and DAG, finding the parent described above.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
