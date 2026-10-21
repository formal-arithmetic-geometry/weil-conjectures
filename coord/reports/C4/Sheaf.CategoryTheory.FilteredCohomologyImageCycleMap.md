## What changed

The proved Sheaf filtered-cohomology-image chain is kept: Image, CycleMap, Normalized,
Presentation and StableSubquotient. The only Lean edit is cosmetic and sits inside the proof of
`CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map`
(`have hTZ : T ≤ Z := by exact inf_le_right`).

The reviewer's FIX restored two files to their live text:
- `Sheaf.CategoryTheory.FilteredStableSubquotient`;
- the node `lem-sp-filtered-stable-subquotient-at-bounds`.

The delivered switch of `stableSubquotient_at_bounds` from `cohomologyImage` to
`homologyFiltration` was not forced. The live module compiles against this delivery.

## Proved and sorry left

No sorry was added, closed or left. `cohomologyImage_cycle_map` (node
`new-cohomology-image-cycle-map`) stays fully proved, with axioms propext, Classical.choice and
Quot.sound.

## No longer needed

Nothing.

## Where the brief, the DAG or earlier work was wrong

The two filtered-cohomology-image chains, Sheaf and WeilConjectures, are twins with the same
names. A partial retirement clashes, so they must be retired as one unit later.

Change record: `coord/changes/retire-filtered-cohomology-image-cycle-map-C4.md`. It says the
retirement is withdrawn and nothing others see has changed.

## Second reading by C4

None. The worker delivers directly; the maintainer's independent review is the reading.
