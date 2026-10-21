## What changed

Retired `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage`, a listed retirement item,
using `deleted.txt`. Its existing adopted source twin
`WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage` proves
`AlgebraicGeometry.exists_flat_module_on_later_stage` with a byte-for-byte identical
public signature. The DIFFERENT retirement marker concerns the removed private helper
`flatOver_of_iso`, which the source twin replaces with the proved public flatness API.

Changed only the private import of the sole direct consumer,
`Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent`, to use that source module.
Kept `lem-pc-flat-module-on-later-stage`, reassigned its Lean attachment to the source
theorem, and updated the parent node's proof step to identify the source realization.
The same node dependencies and unit route remain; no source-library file is changed.

Validation: the original item compiles. A separate import of the source twin confirms
its declaration and prints exactly `propext`, `Classical.choice`, and `Quot.sound`
for its full axiom closure. The source theorem signature is byte-for-byte identical
to the retired theorem. The import-direction check allows the consumer's new import.
The adapted consumer is compiled through lcompile and checked again by deliver3.

Change record: `coord/changes/C7-flat-module-on-later-stage-upstream-retirement.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Holes left: 0.
No new theorem or split-off obligation is introduced. The existing source theorem
`AlgebraicGeometry.exists_flat_module_on_later_stage` is fully proved, including
its dependency closure, as confirmed by its axiom probe.
This delivery is a duplicate retirement, not a newly closed proof hole.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage`. Removed its duplicate
public theorem and its five private proof helpers. Removed the consumer's private
import of this module and replaced it with the corresponding source import.
The duplicate module's four public imports and four private proof imports disappear
with it; the existing source twin supplies the same theorem with its own imports.
No mathematical node or transitive proof dependency is claimed unnecessary: the source
theorem still uses finite-presentation descent, finite affine chart flatness descent,
finite directed bounds and tensor-pullback composition. The child and parent DAG
nodes and their edges remain intact, so no unfinished parent obligation is discarded.

## Where the brief, the DAG or earlier work was wrong

This assignment is already proved in both trees and is listed in `coord/retire-items.tsv`.
The old node attachment and sole Sheaf consumer still selected the duplicate. The
shortest route is the existing adopted source theorem, whose axiom closure has no holes.
The node is now attached there. No mathematical statement was disputed or changed.
The current rework and return records contain no restoration or review request for
this item. The parent has no claim in the shared claim records; its sole changed line
is required to migrate the import away from the withdrawn module.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
