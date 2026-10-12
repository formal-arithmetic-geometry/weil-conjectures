## What changed

The target theorem now combines two named component theorems, one for the relative
singular ideal inclusion and one for the absolute inclusion. The combination is proved by
constructing the conjunction from the two component applications. Two new modules and DAG
nodes were added; their proofs remain explicitly split as documented sorries.

## Proved and sorry left

`Algebra.singularIdeals_of_annihilator_bound` is proved by applying the two component
inclusions. Sorries remain in `Algebra.singularIdeal_map_le_relative_of_annihilator_bound`
(node `lem-weil-pbc-singular-ideals-relative-bound`) and
`Algebra.singularIdeal_map_le_absolute_of_annihilator_bound`
(node `lem-weil-pbc-singular-ideals-absolute-bound`).

## No longer needed

No imports or existing nodes were pruned; the original target's proof dependencies are
encapsulated by the two component nodes.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires substantial flat-base-change, finite-support, and smooth
composition infrastructure that is not available as proved declarations in this closure.
The target was therefore decomposed into its two strict component inclusions, each matching a
separate step of the stated argument.

## Earlier second reading (a previous round; superseded)

Pending second reading by the Y2 reviewer.

## New nodes

`lem-weil-pbc-singular-ideals-relative-bound` records the relative inclusion component.
`lem-weil-pbc-singular-ideals-absolute-bound` records the absolute inclusion component.

## Second reading by Y2

1. **Interface unchanged.** Compared `lean/Sheaf/RingTheory/SingularIdealsOfAnnihilatorBound.lean` with the repository version; its theorem statement and all existing declarations are byte-for-byte unchanged. The only item-module change is replacing the target proof with the conjunction of the two component applications.

2. **Compilation and proof audit.** Compiled all three delivered modules with `lcompile.py --all`; compilation succeeds. The target theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The two component theorems intentionally retain their documented `sorry`s and corresponding split nodes; no `sorry` occurs in a definition.

3. **Split statements.** Read both component statements and their docstrings against the source argument. Each is a strict, mathematically meaningful component (relative and absolute containment), with the exact hypotheses and conclusion used by the target. The nodes and declarations agree, and no duplicate library theorem was found in the imported closure.

4. **Pruning and route.** The target proof uses both component declarations, so both imports are required. No prior proof dependency or import can be removed. The component modules expose only the declarations needed by the target, and the unit route is preserved by the conjunction proof.

5. **DAG consistency.** Verified the target and both split nodes identify the delivered modules and declarations, with matching statements, sources, proof origins, and split status. No statement or definition was changed.

Changed during second reading: added this review section only; no Lean declarations, statements, definitions, imports, or DAG nodes were altered.
