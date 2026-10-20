## What changed

Repaired the upstream-sync quarantine of
Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality and its sole
quarantined consumer Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentNaturality.
Each compatibility path now publicly re-exports its canonical WeilConjectures twin.
Both complete proofs already exist upstream, so the shortest route is to use them.
The two DAG attachments now name the upstream modules and current signatures.
Change record: coord/changes/canonical-tensor-hom-chain-upstream-reexports.md.

Reconciled returned delivery d2c797c18 against current sheaf-dag dba334d2528.
At this base both Sheaf paths remain absent from lean/ and preserved in
quarantine/; neither approved compatibility file was merged. The current upstream
files match their quarantined proofs modulo the copyright header, Sheaf-to-
WeilConjectures imports, and IsAcyclicTensorKFlat-to-IsKFlatTensor rename.
Retained the reviewed re-export repair on this current source instead of restoring
stale duplicate declarations. The delivery tool builds its replacement commit
on the freshly fetched sheaf-dag base. Both restored modules passed individual
server compilation and the sandbox import-order compile with exit code 0.

## Proved and sorry left

Zero holes before, zero holes after; zero holes closed and zero holes added.
AlgebraicGeometry.tensorHomUncurry_chain_natural and
AlgebraicGeometry.tensorHomUncurry_descent_natural are supplied by their complete
upstream proofs. No theorem is split off. This is an actual compilation repair:
the quarantined chain module used the nonexistent IsAcyclicTensorKFlat field
against its canonical imports. No sorry remains in either restored module.

## No longer needed

Removed the local duplicate theorem implementations and private helpers.
The chain compatibility module no longer imports
WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential,
WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation,
Sheaf.Algebra.Homology.KFlatResolution, or Sheaf.Algebra.Homology.KInjectiveHomComplex
separately; its canonical upstream proof supplies the necessary dependencies.
The descent compatibility module no longer separately imports
WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential,
Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryChainNaturality, or
Mathlib.Algebra.Homology.DerivedCategory.Fractions.
No mathematical proof-dependency node is pruned: the canonical proofs follow the
same K-flat representative, K-injective lift, localized evaluation and roof
transport route. Only the two duplicate Sheaf implementations are superseded.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because the upstream sync moved it to
quarantine/, as recorded in coord/rework.tsv. It has zero textual sorry, rather
than the anticipated unfinished proof. The reported compiler error is the
IsAcyclicTensorKFlat rename to IsKFlatTensor. Both corresponding upstream proofs
already implement the planned argument. The old DAG module attachments and
signatures still named the quarantined copies and obsolete predicate.

The C-d2c79 review passed, but landing rejected the old packet because its item
path changed after base d92f73d8e. This retry rechecks the current source and
quarantine records and compiles the retained repair on the current server build.
The live library has no direct importer of either compatibility path; the only
quarantined direct importer is the included descent module, which is unclaimed.
The archives are retained and no path is listed for deletion.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
