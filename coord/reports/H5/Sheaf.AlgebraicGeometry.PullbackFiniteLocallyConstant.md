## What changed

Completed the retirement explicitly listed in `coord/retire-items.tsv`. Withdraw
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant` in favour of the existing
`WeilConjectures.AlgebraicGeometry.PullbackFiniteLocallyConstant`. The retired file
had no textual sorry and already compiled; this delivery removes a duplicate rather
than claiming a newly proved theorem.

Redirected the private proof import in four consumers, preserving `import all` in the
two consumers using the private `finiteLocallyConstant_of_iso` helper:
`ConstructibleEtaleSetPullbackStratum`, `FrobeniusVectorBundleKernel`,
`IrreducibleLisseRefinement`, and `LisseStratumInteriors` (all under
`Sheaf.AlgebraicGeometry`). Every other byte of their Lean source is unchanged.
All four compile separately through lcompile.py. The unchanged transitive consumer
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` compiled unchanged against the overlay (19.5 seconds).

The upstream signatures use `IsFiniteLocallyConstantSheafOfTypes`; the old signatures
use its abbreviation `IsLisseEtaleSheafOfSets`. A scratch file applies the upstream
main theorem and isomorphism helper to the exact old signatures; both compile and
use only propext, Classical.choice and Quot.sound. Reattached the main
DAG node to the upstream theorem, recorded the upstream proof's proved geometric-stalk
comparison dependency, and changed the stratum node's helper-provider reference.
The main mathematical statement and all parent dependencies remain intact.

Change record: `coord/changes/retire-pullback-finite-locally-constant-H5.md`.
No new nodes, definitions, axioms or source-library edits.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No declaration with sorry remains in the item or is added elsewhere.
The existing proved `AlgebraicGeometry.Scheme.pullback_finite_locally_constant` and
private `AlgebraicGeometry.Scheme.finiteLocallyConstant_of_iso` are supplied by the
upstream twin, with definitionally identical signatures. The other three private
helpers of the duplicate are removed with that module; their upstream versions stay.
This is a completed listed retirement, not a proof-hole reduction or decomposition.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`.
Its four direct import references are replaced by the upstream provider. The retired
module's direct imports (EtaleSheaves, EtaleInverseImageAbelianLift, AB5 types,
Functor.Flat and ConstructibleSheaf.Pullback) need no duplicate import path through
Sheaf; the upstream implementation imports the same APIs as needed. No mathematical
DAG node is withdrawn or pruned: existing parents still need this result, now attached
to the upstream proof. The fixed unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof item, but the current retirement list explicitly
assigns this module as a depth-zero retirement with zero holes. It is already proved.
The DIFFERENT classification comes from spelling the same predicate by its canonical
name upstream and from using the proved algebraically-closed/separably-closed stalk
comparison internally; it does not require weakening or strengthening a consumer.

Read the source statements, both complete proofs, the unit record and Stacks' local
etale-cohomology source for the pullback-local-constancy lemma. Searches via launcher
LeanFinder, Loogle and grep found no Mathlib replacement; repository search found the
exact existing upstream implementation, which is reused. Empty covers and empty stalks
require no extra choice or nonemptiness hypothesis. The unit has no realized statement
or step replaced by this retirement.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
