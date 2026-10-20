## What changed

Retired Sheaf.Algebra.Homology.LocalizedTensorComparisonConeRows, the zero-hole
retirement item assigned by coord/queue.tsv and coord/retire-items.tsv.
Reattached lem-pc-localized-tensor-comparison-cone-rows to the proved adopted
source theorem ModuleCat.exists_localizedTensorComparison_cone_rows in
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonConeRows.
The source theorem has the identical conclusion with the unnecessary hQ, hK₁
and hK₂ hypotheses omitted. Its proof follows the existing DAG plan verbatim.
The node's mathematical statement and dependencies remain unchanged.

Change record: coord/changes/C9-retire-localized-tensor-comparison-cone-rows.md.
No source-library module or target statement was changed.

## Proved and sorry left

Original holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry declarations remain in the retired item or are added by this delivery.
The preserved source theorem already has a complete proof. The scratch theorem
ModuleCat.old_cone_rows_signature reproduces every former hypothesis and the
full former conclusion and proves it by applying the source theorem. Its remote
compile passed in 7.3 seconds. Both it and the source theorem use only propext,
Classical.choice and Quot.sound, as verified by #print axioms.
An initial extra compile of the unchanged source five-term-diagram module timed
out at 60 seconds. A diagnostic repeat with the development profiler enabled
passed in 51.8 seconds; it emitted only the expected scratch profiler-option
warning. It is not a consumer of the retired Sheaf module, and its source and
imports remain unchanged. The former-signature test above directly verifies the
only API difference relevant to retirement.

## No longer needed

Pruned module: Sheaf.Algebra.Homology.LocalizedTensorComparisonConeRows.
There are zero current importers of this copy, confirmed by downstream.py and
whole-library and quarantine searches. The retirement table's historical Sheaf
consumer is already absent. Its existing DAG node attaches to the adopted
WeilConjectures.Algebra.Homology.LocalizedTensorComparisonTriangleFiveTermDiagram,
which already imports and applies the source theorem with the current arguments.
The parent cone-row dependency remains valid through the updated attachment.
No parent proof, dependency list or unit route is bypassed.

The retired copy's public imports were Mathlib.RingTheory.Flat.Basic and
WeilConjectures.Algebra.Homology.TensorConeFiveTermExact. Its proof imports were
WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyTriangleRows,
WeilConjectures.Algebra.Homology.TensorCoefficientConeBoundary and
WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated.
All these ingredients remain needed by the preserved source proof. This delivery
claims no pruning of their modules or nodes. No DAG node is removed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole or repairing an assigned defect.
The actual queue assigns retirement of a zero-hole duplicate. The old retirement
inventory lists a consumer that has already migrated to its adopted source twin;
current source and quarantine searches find no remaining Sheaf import to adapt.
The apparent API difference is exactly the removal of three unused K-flatness
hypotheses upstream; the compiled former-signature specialization verifies that
it does not prevent retirement. Zero rings, zero maps, arbitrary complexes and
all degrees are covered because this specialization restricts none of them.

Searches through msearch.py found the generic Mathlib connecting-map naturality
lemma and mapping-cone homology tools, with no specialized cone-row comparison.
Local library searches found the already proved stronger adopted theorem.
The node's three proof steps still describe that theorem: distinguishedness of
the tensored cone and model rows, three tensorator naturality squares, and the
coefficient boundary square. No new mathematics, theorem or DAG node is needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
