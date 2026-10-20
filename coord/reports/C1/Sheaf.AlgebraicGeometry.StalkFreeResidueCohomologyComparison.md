## What changed

Restored Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison from the quarantine
archive listed in coord/rework.tsv. Replaced the private Sheaf KFlatResolution and
KFlatStalkCriterion imports with their existing WeilConjectures equivalents. This makes
the chosen resolution and stalk criterion use the upstream IsKFlatTensor predicate
required by the restored residue-comparison dependency. The theorem signature, public
imports, complete proof body, DAG attachment and unit route are unchanged.

The server compiled the restored residue-comparison dependency (unchanged source,
7.8 seconds) and the repaired item (3.8 seconds). The temporary dependency source was
removed from the sandbox after validation; it is not part of this delivery.
Change record: coord/changes/C1-stalk-free-residue-current-kflat-imports.md.

## Proved and sorry left

AlgebraicGeometry.Scheme.nonempty_stalkFree_residueCohomology_linearEquiv has a complete
compiling proof. This is a zero-hole quarantine/interface repair: the archived item had
0 sorries, the repaired item has 0 sorries, 0 holes closed, 0 holes added, and 0 split off.
No other declarations are changed. There are no sorries left in the delivery.

## No longer needed

Removed private imports Sheaf.Algebra.Homology.KFlatResolution and
Sheaf.Algebra.Homology.KFlatStalkCriterion, using their upstream implementations instead.
All mathematical proof dependencies remain needed. No DAG node or mathematical module
is withdrawn or claimed as pruned. No unused public import is removed.

## Where the brief, the DAG or earlier work was wrong

The assignment is a quarantine repair rather than a theorem with a current proof hole.
The archived file was blocked on the missing KFlatStalkResidueCohomology artifact; that
dependency has now been restored. Its current hypothesis uses upstream IsKFlatTensor,
while the archive's two local proof imports use the older IsAcyclicTensorKFlat interface.
The upstream modules already provide the exact needed resolution and stalk criterion.
The proof plan still applies verbatim. The general independent-coefficient resolution
recorded at lem-pc-kflat-resolution is stronger than needed here: the existing upstream
resolution specializes directly to the scheme's equal-universe Zariski site.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
