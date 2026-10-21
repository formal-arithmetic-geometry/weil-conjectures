## What changed

Retired Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore
under its explicit coord/retire-items.tsv assignment. The unchanged upstream
module proves the same conclusion without the unused C-flatness assumption.
Reattached lem-pc-localized-tensor-comparison-closure-retracts-core to that
upstream declaration, recording its actual signature. Migrated the sole
consumer, Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetract,
to the upstream proof import and argument list. A specialization lambda retains
its hC binder; every public signature and public import remains unchanged.

Change record:
coord/changes/Q2-retire-localized-tensor-comparison-closure-retract-core.md.

Validation: the original item compiled. The adapted consumer compiled without
warnings in 3.0 seconds via lcompile.py. A separate probe printed only propext,
Classical.choice and Quot.sound for the upstream core theorem. Live and
quarantined import searches and downstream.py identify exactly one direct
consumer. No item rework entry or consumer claim file exists in this snapshot.

## Proved and sorry left

Original item: zero direct holes. Closed zero holes, added zero holes, left zero
holes in the retired item and adapted consumer. This is duplicate retirement,
not a new proof or a decomposition.
ModuleCat.localizedTensorComparisonProperty_retract_core stays fully proved
upstream, and ModuleCat.localizedTensorComparisonProperty_closure_retracts
keeps its complete proof with its exact original statement.

## No longer needed

Pruned the duplicate module
Sheaf.Algebra.Homology.LocalizedTensorComparisonClosureRetractCore and removed
its proof-only import from LocalizedTensorComparisonClosureRetract. Its private
exists_kFlat_representative duplicate disappears with the module; the complete
upstream helper remains. No mathematical node or proof dependency is removed:
the core node now names its upstream proof, whose K-flat representatives,
derived-arrow functor and retract argument remain needed. No other module is
withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished obligation, but the actual
queue and retirement table assign removal of an already proved duplicate.
The upstream interface drops hC. An import-only migration was tested and failed
at old line 56: hC : Module.Flat (A tensor_R B) C was supplied where hQ's
acyclic-tensor predicate was expected. The delivered call fixes that mismatch
without altering the consumer's signature or weakening any conclusion.

A parsed search of all DAG dependency fields finds no incoming logical edge
to the core node; the existing Lean consumer is migrated in this packet. The
core node, its dependencies and the unit's empty realized lists are preserved.
The source's retract argument and the upstream proof agree: use K-flat
representatives, compare their arrows by the derived functor, and apply
stability of isomorphisms under retracts. Identity retracts, zero objects and
zero rings require no extra hypotheses. No false statement was found.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
