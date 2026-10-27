## What changed

Completed the assigned zero-hole import repair in three modules:
Sheaf.AlgebraicGeometry.QCohTensorResolutionTotalCoherence now explicitly imports its
Sheaf RestrictionCoherence and TotalComponents companions as well as the canonical
source TotalCoherence module. The two unclaimed companions now re-export their proved
source implementations. Their previous duplicate declarations prevented combining the
item with its former dependency paths.

The change record is coord/changes/B2-qcoh-total-coherence-companion-imports.md.
All three delivered modules compile without warnings. All six companion theorem
signatures match the original signatures; the reassoc lemmas remain available.
The original mixed-import regression fails with a duplicate
TensorResolutionRestrictionCoherence_localInst1, even with the latest TensorNaturality
repair present. The same mixed-import regression compiles after this repair. Axiom checks of all three total
coherence declarations, all six companion theorems and the three reassoc lemmas report
only propext, Classical.choice and Quot.sound.
The unchanged archived HomologyCoherence consumer also compiles against the repaired
modules in 59.1 seconds; its existing unscoped-option and long-line warnings remain
only in that scratch check. No consumer changes are delivered.

## Proved and sorry left

This is a zero-hole rework: 0 original holes, 0 closed, 0 added, 0 split off,
0 remaining in any delivered module. No declaration with sorry is left or introduced.
The existing proved total coherence identities and companion component/restriction
lemmas are supplied by their canonical source declarations. This is an import repair,
not a new proof or a decomposition.

## No longer needed

Duplicate Sheaf implementations in QCohTensorResolutionRestrictionCoherence and
QCohTensorResolutionTotalComponents are replaced with their canonical source imports.
The former explicit imports of the source ChartRestriction and the Sheaf
TensorNaturality modules in those companion files are supplied transitively by the
canonical modules. No mathematical lemma, DAG dependency, unit step or module is pruned;
no module is withdrawn. The canonical source proofs keep all required mathematics.

## Where the brief, the DAG or earlier work was wrong

The rework list still describes the original quarantine failure, although the F1
restoration has already landed and the current item contains zero sorry. Repeating
that restoration would be a no-op. The remaining reproducible defect is the import
collision between that restored source path and its old explicit Sheaf companion
paths, whose duplicate implementations F1 left in place.

There is no direct DAG attachment for these helper modules. The existing parent
new-t3-qcoh-tensor-resolution-chart-comparison-naturality continues to use
AlgebraicGeometry.tensorResolutionChartRestriction_total in proof step 3 with exactly
its existing meaning. No new node, mathematical statement or source-library edit is
needed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
