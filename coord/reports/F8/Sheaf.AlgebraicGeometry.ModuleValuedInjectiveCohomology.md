## What changed

Retired Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology under the
human-authorized retirement list. Its official upstream twin proves the same
conclusion with an additional underlying-abelian-sheaf isomorphism. The DAG node
new-module-valued-injective-cohomology-comparison now points to that theorem,
records its exact signature, and explains how to discard the extra conjunct.
The mathematical statement, proof dependencies, parent dependencies and unit route
remain unchanged. No upstream source or target statement changes.

The original module compiled cleanly in 5.5 s. A separate Lean check proves its
exact original statement from the upstream theorem, with only propext,
Classical.choice and Quot.sound; the upstream theorem has the same axiom list.
Unchanged copies of ModuleAcyclicEffacementLadder, ModuleAcyclicCohomologyComparison
and AlgClosedExtensionInjectiveAcyclic compile cleanly through lcompile.py.

Change record: coord/changes/F8-retire-module-valued-injective-cohomology.md.

## Proved and sorry left

This is a retirement with zero original holes: closed 0, added 0, split off 0,
remaining 0. AlgebraicGeometry.Etale.moduleValued_injective_cohomology_comparison
was already proved in the copy and is proved without sorry dependencies upstream.
The exact old statement follows by projecting away the extra isomorphism conjunct;
that implication was separately checked by Lean. No new declaration is delivered.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.ModuleValuedInjectiveCohomology.
No current consumer imports it, so no consumer import edit is needed. The listed
former consumer Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder is already
retired and its upstream replacement uses the official theorem.

The withdrawn copy's imports are
WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance,
Mathlib.Algebra.Category.ModuleCat.Sheaf,
Mathlib.CategoryTheory.Abelian.RightDerived,
WeilConjectures.AlgebraicGeometry.ConstantRingModuleSheafEquivalence, and
WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation.
They remain needed by the official proof: none is claimed globally pruned.
No mathematical dependency node is pruned; the comparison node and both parents'
references remain valid through the upstream attachment.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief names a module which currently contains no sorry.
Its active task is the explicit retirement row in coord/retire-items.tsv.
That table's consumer information is stale: the Sheaf effacement-ladder consumer
is already absent, its node points upstream, and the upstream consumer already
handles the strengthened four-component conclusion. The comparison node alone
still pointed at the old copy; this delivery repairs that attachment.
No mathematical error was found in either comparison statement.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
