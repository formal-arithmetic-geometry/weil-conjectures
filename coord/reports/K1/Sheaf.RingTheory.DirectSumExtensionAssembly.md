## What changed

Retired `Sheaf.RingTheory.DirectSumExtensionAssembly`, a depth-zero retirement item
in `coord/retire-items.tsv`. Its upstream twin already proves the identical theorem
with the same universes; only hypothesis binder names differ. Changed the only
consumer, `Sheaf.RingTheory.TorsionExtensionFlatDescent`, to import the upstream
module. Its positional application needs no adaptation. Repointed the existing
DAG node's Lean attachment and recorded the exact upstream signature.

Change record: `coord/changes/retire-direct-sum-extension-assembly.md`.
The original item compiles without holes. The adapted consumer is compiled alone
and the delivery probe checks its axioms. No source-library module is changed.

## Proved and sorry left

Zero holes before and after. Closed: none. Added: none. Split off: none.
`LinearMap.extension_descends_of_summands` remains fully proved by the upstream
theorem, including its proved Ext-one direct-sum dependency. The withdrawn private
helpers `LinearMap.glue_extension_maps` and `LinearMap.extension_map_ext` were
already fully proved; their upstream counterparts remain in the upstream proof.
No `sorry` remains in either delivered module.

## No longer needed

Pruned module: `Sheaf.RingTheory.DirectSumExtensionAssembly`.
Removed consumer import: `Sheaf.RingTheory.DirectSumExtensionAssembly`; replaced
with `WeilConjectures.RingTheory.DirectSumExtensionAssembly`.
The withdrawn copy's Mathlib imports and `WeilConjectures.Algebra.ExtOneDirectSum`
proof import remain in the upstream twin. No mathematical dependency node is
pruned: the same proof and the unit route remain valid. The existing node
`lem-weil-pbc-direct-sum-extension-assembly` now attaches to the upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief suggests a proof hole, but this item is the zero-hole
retirement listed in `coord/retire-items.tsv` and described by the human's hand-off
in `coord/changes/retire-sheaf-twins-20261020.md`. The DIFFERENT classification is
only a hypothesis-binder rename; the theorem is not mathematically restated.
No new theorem, definition, axiom, or DAG node is introduced.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
