## What changed

Completed the explicit zero-hole retirement of
Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift from coord/retire-items.tsv.
Listed the duplicate in deleted.txt and reattached
lem-sc-perfect-stalk-derived-hom-lift to the exact existing source declaration in
WeilConjectures.AlgebraicGeometry.PerfectStalkDerivedHomLift, with existing:true.
The node's proof identifies the source canonical comparison construction; its
mathematical assertion, dependencies, unit and parent edges remain unchanged.
Change record: coord/changes/Q2-retire-perfect-stalk-derived-hom-lift.md.

The source theorem is stronger: it omits hU and fixes cG and cH canonically.
A scratch proof of the entire original signature chooses these comparisons as
the existential witnesses and uses the source chain map and equality. It compiles.
The source parent's proof already imports and uses this canonical source theorem;
no consumer adaptation or source-library edit is required.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. Sorries left: none.
This delivery completes a retirement repair, not a new hole-closing proof.
AlgebraicGeometry.Scheme.exists_affine_perfect_stalk_hom_lift and
AlgebraicGeometry.Scheme.perfectLocalModelStalkComparison are already proved in
the source library. Explicit #print axioms checks of both and the compatibility
proof show only propext, Classical.choice and Quot.sound.
The original duplicate compiled before withdrawal. tools/downstream.py --uses
reports zero downstream modules and only the duplicate's own declaration reference. The unchanged source parent
is checked independently through lcompile.py. No axioms or new declarations,
hollow definitions or data chosen from an unproved existence theorem are added.

## No longer needed

Withdrawn: Sheaf.AlgebraicGeometry.PerfectStalkDerivedHomLift, including its private
map_strictlyPerfect_of_mapFree and local_model_stalk_comparison proofs. No live or
quarantined module imports that Sheaf module. Its old inventory consumer has already
been retired; the actual source parent imports the source theorem directly.

The duplicate's direct imports disappear with it:
WeilConjectures.AlgebraicGeometry.PerfectComplex,
WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor,
WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative,
WeilConjectures.AlgebraicGeometry.PerfectOpenStalkDerivedHomDescent, and
WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso.
Those source modules remain needed by the source implementation. No dependency
node or unit statement is pruned; only the redundant Sheaf module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but the current assigned queue row
is retire with zero holes. The live source theorem is stronger than the duplicate,
so the correct repair is retirement with source reattachment, not a new reduction.
The stale inventory names the now-absent Sheaf parent; the current DAG parent is
already attached to the source module and its actual proof uses the source theorem.
The mathematical dependency remains justified and present; zero importers alone
is not used as a reason to discard the node.

The original signature is implied verbatim, as checked in Lean. Zero complexes,
zero ranks, arbitrary schemes, and independent derived universes are covered;
hxU excludes the empty-open edge case. The source proof follows the same exact
stalk comparisons, derived Hom descent, affine chain representatives and naturality
route. The unit record is unchanged. No target statement changes.

Searches made with msearch.py: leanfinder on derived stalk morphisms lifting to
chain maps (eight general spreading-out/derived fraction hits); loogle on stalk
(twelve ring-map stalk-surjectivity hits); grep on perfect/stalk/hom combinations
(one unrelated structure-sheaf hit). Local rg finds the exact stronger source
theorem, which is used. The source and duplicate signatures, complete proof bodies,
sole DAG parent and unit realization record were read directly.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
