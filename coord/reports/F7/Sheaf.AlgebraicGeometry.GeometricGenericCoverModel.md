## What changed

Completed the listed retirement of
`Sheaf.AlgebraicGeometry.GeometricGenericCoverModel` using the existing source
module, not a new proof split. `deleted.txt` withdraws the duplicate module.
Reattached `lem-sbc-geometric-generic-cover-model` to
`AlgebraicGeometry.exists_geometric_generic_cover_model` in
`WeilConjectures.AlgebraicGeometry.GeometricGenericCoverModel`.
The project's parser reports identical main theorem statements.

Updated the main node's empty-index proof to match the retained source proof:
its proved private empty-fibre lemma invokes closed avoidance directly. This
removes its dependency on the more general Sheaf-only model-data helper.
With that helper's only parent removed, cleared its Lean attachment and obsolete
proof edges. All DAG nodes and their mathematical statements are retained.
Change record: `coord/changes/F7-retire-geometric-generic-cover-model.md`.

The only actual DAG parent of the main theorem is the cover-spreading theorem,
whose Lean module already imports and applies the retained source declaration.
No source-library file, target, statement, definition or unit route is changed.

## Proved and sorry left

The starting item has **zero** theorem holes. Closed **0 of 0** holes; added **0**
holes; split off **0** statements. No `sorry` remains in the withdrawn item or
is added anywhere in this delivery. This is a duplicate retirement, not a claim
of new theorem-proof progress.

The surviving `AlgebraicGeometry.exists_geometric_generic_cover_model` has exactly
`propext`, `Classical.choice` and `Quot.sound` as axioms. Its consumer
`AlgebraicGeometry.exists_open_spreading_geometric_generic_cover` likewise has
only those three axioms. Checked both with `#print axioms` through `lcompile.py`.
The initial unchanged Sheaf file also compiled without warnings. Recompiled the
retained source model (4.1 s) and its unchanged source consumer (3.8 s), each
within the single-file limit and without warnings, through `lcompile.py`.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.GeometricGenericCoverModel`.
Retired Sheaf-only helper:
`AlgebraicGeometry.exists_geometric_generic_cover_model_data`, node
`new-lem-sbc-geometric-generic-cover-model-data`. No actual DAG parent remains
for this helper after updating the main proof, and there is no unit realization
of it. The historical node remains; its `lean` attachment is explicitly null.

Withdrawing the duplicate removes all of its imports:
`Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance`,
`WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`,
`WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread`,
`WeilConjectures.AlgebraicGeometry.CompatibleEtaleGenericFibreModel`, and
`WeilConjectures.AlgebraicGeometry.ClosedFamilyGeometricFibreShrink`.
These imports are still needed by the retained source proof; no other module
or dependency node is claimed globally unnecessary. The main node is preserved
on the existing source theorem, rather than pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with holes or a repair. The current
item is instead a listed retirement with zero holes. `coord/retire-items.tsv`
identifies the substantive duplicate and the missing upstream helper. The older
kept-twins warning about mixed dependency environments is stale for this item:
its dependency imports and its only mathematical consumer already use the source
library. The source consumer compiles with that source theorem.

The DAG attachment still named the Sheaf duplicate, and its proof cited the
Sheaf-only model-data helper. The source proof has the same main conclusion and
handles empty I directly through a specialized private lemma. The updated node
records this actual route. The helper has no consumer apart from the removed
edge; blueprint ancestry occurrences were distinguished from actual statement,
proof and proof-step dependencies. All source statements are preserved, including
the full field-base-change irreducibility and generic-intersection conclusions.
The empty-index case and the nonempty-index closure/shrinking argument remain.
No unit statement or proof step is bypassed.

Searched using LeanFinder, Loogle and Mathlib grep via `msearch.py`; none returned
a matching Mathlib theorem. Repository search found the exact source-library
statement. Direct source comparison, consumer inspection, the dependency-field
scan, and the standard-axiom checks validate that replacement.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
