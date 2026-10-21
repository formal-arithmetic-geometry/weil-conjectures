## What changed

Restored the assigned quarantined module as a public adapter to
WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons and the
existing Sheaf stage-equivalence compatibility adapter. The canonical source supplies all
shared constructors and their theorems. Retained and proved the four additional archived
component theorems, with unchanged signatures. No adopted-source file is modified.

The inverse-square equation follows by expanding the named comparisons and identifying
their identical pinned composition family. Inverting that equation gives its forward
version. Rewriting the existing beta component formulas proves the remaining two equations.
This argument is uniform for empty/equal opens and arbitrary derived objects.

The adapter compiled on the project server in 12.3 seconds without warnings after removing
unused private proof imports. The existing node attachment and all dependencies are retained;
its proof and origin now describe the adapter. The seven archived direct consumers and five
DAG parents were checked for preserved names/signatures. The temporary StageTransport
constructor probe is described in the change record; other archived consumers retain
independent quarantine dependencies and are not claimed to compile here.

Change record: coord/changes/u9-perfect-overlap-core-comparisons-adapter.md.

## Proved and sorry left

Assigned definition repair: 0 original sorries, 0 remaining, 0 added, 0 split off. No hole
closure is claimed. The restored adapter proves these existing theorems:

- AlgebraicGeometry.openPullbackRestrictionIso_inv_app_eq_square
- AlgebraicGeometry.openPullbackRestrictionIso_hom_app_eq_square_inv
- AlgebraicGeometry.perfectOverlapRestrictionBeta_hom_app_square
- AlgebraicGeometry.perfectOverlapRestrictionBeta_inv_app_square

They belong to def-pc-perfect-overlap-core-comparisons-api. All other archived public
comparison declarations are supplied by the public source import, rather than redeclared.

## No longer needed

Removed direct archive imports of:

- WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
- Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
- Sheaf.AlgebraicGeometry.PerfectHomTransport
- WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
- WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
- WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
- Sheaf.AlgebraicGeometry.DerivedPullbackComposition
- WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
- WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent
- Sheaf.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract

The canonical source import already supplies their required source declarations. In
particular the retired Sheaf cancellation module and hollow reexports of transport must
not be used to reconstruct duplicate public names. Two experimental `import all` proof
imports were also removed after successful compilation without them. The stage-equivalence
adapter remains publicly imported to preserve its additional component API.

No mathematical node or parent dependency is pruned: the adopted-source construction still
uses the original construction/localization dependencies. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The queue's generic count of one hole is not the archive's actual hole count: this is a
zero-sorry quarantined repair. The archive is not usable unchanged after synchronization:
its shared names already exist upstream, some old Sheaf imports have been retired, and the
canonical stage-equivalence adapter imports the source versions. Importing the source
comparison module and retaining only the four missing helpers resolves those collisions
without changing target statements or dropping the quarantined attachment.

The historical cancellation retirement record says all consumers are upstream; the
quarantined comparison archive still imports the retired copy. This restoration repairs
that obsolete edge. The Mathlib search found NatIso.naturality_1 as the exact replacement
already used by the adopted source. LeanFinder, Loogle and grep searches were run through
msearch.py. The original archive compile request received no answer from the busy server;
subsequent adapter compiles succeeded, so this was not treated as a tool blocker.

The archived StageTransport attribute failure is independent of this adapter's theorem
statements. Its temporary constructor probe omits that redundant attribute only; no repair
of another quarantined item is included here.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
