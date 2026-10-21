## What changed

Completed the listed retirement of
`Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`. Withdraw its duplicate
`AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_stratum` in favour of the
existing proved declaration in the upstream module of the same suffix. Reattached
`lem-stage3-finite-lc-pullback-stratum` to that existing declaration. Both complete
proofs implement the same five-step fixed-stratum argument; no route is replaced.

The upstream predicate is `IsFiniteLocallyConstantSheafOfTypes`; the old predicate
`IsLisseEtaleSheafOfSets` is its abbreviation. The full former signature is accepted
by direct application of the upstream theorem in scratch Lean. The original Sheaf
file also compiled cleanly. The unchanged upstream parent module compiled separately
through lcompile.py in 3.5 seconds. The upstream theorem and unchanged parent
`isConstructibleEtaleSheafOfSets_upperStar` have only the three permitted axioms.

There are no active importers of the Sheaf copy, including in quarantine. The sole
DAG parent retains its dependency on this node; its existing upstream Lean module
already imports the upstream stratum module and applies the same theorem. No parent
source or dependency edge needs changing. No upstream file or target is edited.

Change record:
`coord/changes/retire-constructible-etale-set-pullback-stratum-N3.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No declaration with sorry remains in the item or is added elsewhere.
The existing proved `AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_stratum`
continues to supply the exact result. This is retirement of a proved duplicate,
not a new proof-hole closure or decomposition.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullbackStratum`.
Its duplicate imports of EtaleSheaves, UpperLowerStar.Defs,
EtaleInverseImageAlgebraicStructures, PullbackFiniteLocallyConstant (`import all`),
and ConstructibleSheaf.Pullback disappear with the copy; the upstream implementation
keeps the imports its proof needs. No mathematical node or proof dependency is
pruned. In particular the fixed-stratum node and all its parent edges remain needed
and now point to the canonical upstream provider.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a proof obligation, but the live item is a zero-hole
retirement explicitly listed in `coord/retire-items.tsv`. The DIFFERENT classification
is predicate spelling only; the same result already exists upstream. The earlier
upstream-sync retirement of the parent already migrated its import, leaving no
consumer adaptations for this packet. The node still pointed at the duplicate.

Read both complete proofs, the sole parent node and its Lean proof, the unit record,
and the retirement authorization. Launcher LeanFinder and Loogle searches found no
Mathlib replacement; direct repository search found the exact upstream theorem.
The unit record has no realized statement or proof step bypassed by this retirement.
Empty strata, schemes, covers and stalks need no new hypotheses.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
