## What changed

Restored `lean/Sheaf/AlgebraicGeometry/UniversalLowestFiberRanks.lean` from the exact
archive named in `coord/rework.tsv`, preserving all three declarations and their
signatures. Replaced the private import of the withdrawn
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` with
`WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition`, where the dependency
node now records `AlgebraicGeometry.exists_derivedPullbackComposition`.

In `AlgebraicGeometry.Scheme.universalLowest_fiber_ranks`, explicitly select
`SheafOfModules.evaluation.{u}` and supply its additive instance via the composite
of the forgetful and presheaf evaluation functors. This repairs the inferred
`u + 1 = u` constraint when transporting the zero cohomology sheaf to its sections.
The original K-flat comparison, bounded flat model, residue pullback and field
extension argument is retained. The node's proof-origin note records the repair.

The complete module compiled cleanly through `lcompile.py` in 35.2 seconds.
Text comparison verified that all declaration signatures are identical to the
archive and that every Lean line is at most 100 characters.

Change record: `coord/changes/C2-universal-lowest-fiber-ranks-restoration.md`.

## Proved and sorry left

This is a listed quarantine repair with **zero original holes**, rather than a new
closure of an unproved statement. Holes closed: 0. Holes added: 0. Holes left: 0.
No statements were split off.

The complete proofs of `AlgebraicGeometry.Scheme.universalLowest_fiber_ranks`
(node `lem-sc-universal-lowest-fiber-ranks`) and its private helpers
`tensor_single_vanishes` and `finrank_sections_of_rank` are restored and compile.
All existing mathematical dependencies are retained. The proof covers rank zero,
an empty T, and b < a without adding hypotheses.

## No longer needed

Removed the private import of the withdrawn, empty module
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`. Its mathematical dependency
`lem-pc-ringed-spaces-derived-pullback-composition` remains needed and is supplied
by the adopted source module. No mathematical node or further module is pruned.
No unused proof imports remain: the six private imports supply respectively
fibre base change, pullback composition, flat-complex pullback, K-flat tensor
comparison, the flat model, and the free-sheaf sections calculation.

## Where the brief, the DAG or earlier work was wrong

The item source was quarantined, not withdrawn or an unproved theorem: its archive
already had a complete proof. The rework row records a duplicate derived-pullback
import failure from the synchronization. Against the current compiled library,
restoring it also exposes the withdrawn composition import and the evaluation
universe inference failure; both are repaired here. The current dependency node
already names the adopted source composition theorem correctly.

Searches through `msearch.py` (LeanFinder, Loogle, grep) confirmed the t-structure
vanishing API, `Module.finrank_baseChange`, and zero homology from a zero middle
term; the archive already uses this route. Direct searches of both source roots
found no replacement of the item theorem.

The sole current Lean consumer is
`Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel`; its archived copy and
the parent DAG node `lem-sc-perfect-universal-lowest-zero-model` also require this
theorem. Its application at lines 79–80 matches the unchanged signature. No
consumer adaptation is caused by this private import/proof repair, and the unit
route is retained. `tools/downstream.py` does not index the absent quarantined
item, so consumers were checked directly in Lean, quarantine and the DAG instead.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
