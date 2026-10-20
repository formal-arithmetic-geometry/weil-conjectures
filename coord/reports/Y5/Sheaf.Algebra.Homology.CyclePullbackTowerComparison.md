## What changed

Retired `Sheaf.Algebra.Homology.CyclePullbackTowerComparison` using `deleted.txt`.
The adopted `WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison` already
contains the same canonical comparison construction and both projection proofs.
A comparison ignoring comments and whitespace confirms that all implementation text
matches after removing the extra, unused `tower_comparison_first` wrapper.

Reattached the four existing DAG nodes to the upstream module and corrected their
proof-origin paths. The first-projection node now names `canonicalComparison` and
`tower_comparison_canonical_first` together instead of the redundant existential wrapper.
The other declarations and dependency edges remain unchanged. No upstream file is edited.

Change record: `coord/changes/Y5-cycle-pullback-tower-comparison-retirement.md`.

Validation: a scratch Lean example reproduces the removed wrapper's exact conclusion
and proves it using the upstream canonical construction and first projection. The
axiom audit of `evaluatedPullbackIso`, `indexedPullback`, `term_step_eq`,
`canonicalComparison`, `tower_comparison_canonical_first`, `tower_comparison_second`,
and `tower_comparison` reports only `propext`, `Classical.choice`, and `Quot.sound`.
The scratch file imports the surviving upstream Core consumer as well. A fresh
compile of that consumer's unchanged source also passes (1.7 seconds).

## Proved and sorry left

Actual initial holes: 0. Holes closed: none (0 of 0). Holes added: none (0).
Sorries left in the withdrawn module: none. No split-off statements or new axioms.
This is the queue's retirement repair, not a new theorem proof or a decomposition.
The canonical comparison, both projection equations, and their combined existential
remain fully proved in the adopted upstream module.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.CyclePullbackTowerComparison`.
Its private stage-transport and evaluation-comparison implementation is duplicate code;
the retained upstream implementation provides the identical construction and proofs.
The unused `CochainComplex.CyclePullback.tower_comparison_first` wrapper is removed;
its statement follows from the retained canonical witness and first projection.
No new wrapper module or alias is introduced.

All three old imports disappear with the retired file:
`WeilConjectures.Algebra.Homology.CyclePullbackTower`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks`.
They remain used by the upstream implementation and are not globally pruned.
All four mathematical DAG nodes and their dependencies remain needed and are kept;
only their duplicate Lean attachment is replaced. The unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an outstanding proof obligation, but the actual
queue row is `retire` with zero holes. `coord/retire-items.tsv` lists one former
consumer, `Sheaf.Algebra.Homology.CyclePullbackCore`; that module has since been
retired. Current source search and `tools/downstream.py` find no remaining importer
of the assigned Sheaf module. The surviving upstream Core already imports the correct
upstream comparison module. No consumer needs modification in this delivery.

The first-projection node's old attachment names the extra existential wrapper,
which the upstream twin omits. Its canonical witness and proved first-projection
equation supply exactly that existential; the updated attachment records both.
No false statement, hollow definition, or target statement change was found.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
