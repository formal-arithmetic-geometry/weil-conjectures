## What changed

Restored `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenClosed.lean`
from its exact archive in `quarantine/`, as assigned by `coord/rework.tsv`.
The live source file was absent after the cluster restore. This delivery restores
all four existing theorems, their complete proofs, and all three public imports
verbatim. It changes no statement, definition, attribute, universe, or proof route.
The archive is preserved. This is a source restoration, not a new proof or a rebase.

The restored file compiles through `lcompile.py` against the published build
(exit code 0, 11.4 seconds, no warnings). Its existing short argument uses the
source-library exact-functor homology API and the sheaf-level open/closed results;
no new intermediate theorem is necessary. The first theorem transports joint
reflection through the exact-derived-functor comparison. The second transports
sheaf-level disjoint-support vanishing through homology and that comparison.
The bounded constructible theorems then use the inclusion compatibility
isomorphisms and faithfulness of the full-subcategory inclusion.

Consumer inspection: `tools/downstream.py --allow-missing --uses ...` finds zero
current live importers. Searching `quarantine/` additionally finds
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange`
and `Sheaf.Paper.CompactificationRefinementLocalizing`. Both use the restored
statements with exactly the archived signatures; neither needs an adaptation.
Neither consumer is restored or withdrawn by this delivery.

Change record: `coord/changes/E4-derived-open-closed-restoration.md`.

## Proved and sorry left

Actual holes in the archived item: 0. Actual holes in the restored item: 0.
Holes closed: none (0 of 0). Holes added or split off: none.

The following already-proved declarations are restored, under namespace
`AlgebraicGeometry.ProEtale.CondensedRing`:

- `jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`;
- `isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`;
- `isIso_of_isIso_boundedConstructibleUpperStar_map_of_isCompl`;
- `isZero_boundedConstructibleUpperStar_obj_openImmersionLowerShriek`.

No theorem is left with `sorry`; no axiom or definition is added.
The delivery tool performs its normal declaration axiom probe before pushing.

## No longer needed

None. All archived imports and declarations are preserved. No node or module is
withdrawn, no dependency is pruned, and no declaration is replaced by `sorry`.
Zero current live importers is not treated as evidence of mathematical redundancy.
The quarantined parent modules remain consumers of the restored results.

## Where the brief, the DAG or earlier work was wrong

This assigned item is a quarantine restoration with zero holes, rather than an
unfinished theorem. `coord/rework.tsv` records the cluster-restore reversal and
its archive. Exact searches of `dag/nodes/` find no Lean module attachment or
reference to this module or its four declaration names; the original module has
no blueprint tags. Thus there is no existing attached node or proof route to
update. No new mathematical declaration or node is introduced.

Search before restoration: LeanFinder query "Exact functors jointly reflect
isomorphisms on derived categories by commuting with homology" returns generic
exact-derived-functor facts; Loogle `CategoryTheory.Functor.mapDerivedCategory`
returns the exact-functor derived construction. The Mathlib grep search for
`jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory|isZero_mapDerivedCategory_obj`
finds no match; the existing project `ExactFunctor.lean` provides both precise
lemmas, already used by the archived proof. Searches of the two source roots and
archive confirm that the four restored declarations have no live duplicate.
There is no mathematical statement dispute or change to the unit route.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
