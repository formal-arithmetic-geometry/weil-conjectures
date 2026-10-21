## What changed

Restored `lean/Sheaf/CategoryTheory/CartanEilenbergAcyclicAbutment.lean` verbatim
from the quarantine path assigned in `coord/rework.tsv`. This restores
`CategoryTheory.exists_cartanEilenberg_acyclic_abutment`, its unchanged statement,
complete assembly proof, four public imports and three private proof imports.

The proof obtains the normalized abutment isomorphisms from
`exists_cartanEilenberg_augmentation_comparison` and the canonical natural
filtration and stable pages from
`exists_grothendieck_canonical_image_filtration`. It then composes the canonical
step formula with `cartanEilenberg_second_image_eq_truncation` to establish the
filtered-total image formula. The final nonnegative-step equality is the
canonical formula specialized to a natural-number index. These are precisely
the three dependencies in the existing node, so no node change is needed.

Validation: the restored module compiled through `lcompile.py` with exit code 0
in 7.7 seconds after the shared dependency artifact became available. The source
is byte-for-byte identical to the quarantine archive, contains zero holes and
respects the 100-character line limit.

Change record: `coord/changes/CartanEilenbergAcyclicAbutment-restoration.md`.

## Proved and sorry left

`CategoryTheory.exists_cartanEilenberg_acyclic_abutment`
(node `lem-sp-ce-acyclic-abutment`) has a complete proof restored from the archive.
The archive contains zero sorries. Holes closed: zero. Holes added: zero.
Sorries left in the restored module: none. No statements split off.
This is a quarantine restoration, not a newly closed-hole claim.

## No longer needed

None. Every existing proof dependency and import is preserved and used. No nodes
or modules are pruned; the quarantined parent
`Sheaf.CategoryTheory.GrothendieckSpectralSequence` still needs this theorem.

## Where the brief, the DAG or earlier work was wrong

The assigned source is absent from `lean/`, but preserved in `quarantine/` as
recorded in `coord/rework.tsv`. Its actual hole count is zero. The DAG statement
and three-dependency proof plan match the preserved Lean proof. The initial
server compile could not load the recently restored dependency
`Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation` because its compiled
artifact had not yet reached the shared build; no dependency is duplicated.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
