## What changed

Restored the quarantined module
`Sheaf.Algebra.Homology.AffinePushforwardCohomologyEdgeIdentity` as a public re-export
of its proved adopted upstream counterpart. The canonical theorem
`AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity` is the archived
statement and proof with six explicit `SheafOfModules.{u}` annotations and the
upstream factorization import. Its three-step argument constructs the natural edge,
cancels the tilde/Gamma unit and counit, and applies ordinary comparison naturality.
The DAG attachment now identifies that existing declaration. Its statement, three
proof steps and proof dependencies retain their mathematical meaning. No adopted
source file changes, and the original quarantine archive is preserved.

Validation: the archived module reproduces the reported duplicate-declaration import
failure. The restored import path compiles cleanly. A scratch importer uses only the
restored public path to prove the full canonical-representative statement with explicit
sheaf universes and the original downstream edge-existence argument, including its
object-equality elimination. An axiom check of the canonical identity theorem reports
exactly `propext`, `Classical.choice`, and `Quot.sound`. The import-direction check
confirms that the public re-export introduces no cycle.

Change record: `coord/changes/affine-pushforward-edge-identity-rework-P1.md`.

## Proved and sorry left

Zero-hole rework: 0 holes before, 0 after, 0 closed, 0 added, 0 split off.
The already proved declaration
`AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity`
(node `lem-pc-affine-pushforward-cohomology-edge-identity`) is reused from the
adopted source library. No delivered declaration contains `sorry`; the reused theorem's
entire axiom closure contains only the three permitted axioms. This repairs the assigned
import collision and consolidates a duplicate; it is not a new hole closure.

## No longer needed

The duplicate local theorem declaration and its proof are no longer needed. The direct
public import of
`WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates` and private
imports of `WeilConjectures.Algebra.Homology.AffineDerivedPushforwardSheafEdge` and
`Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` are replaced by the
single public upstream identity-edge import. The upstream provider publicly imports
the same coordinate API and privately uses the same sheaf edge and canonical
factorization. These three dependency nodes and their mathematics remain needed.
No node, dependency or library module is claimed as pruned, and nothing is withdrawn.

## Where the brief, the DAG or earlier work was wrong

This is a quarantined zero-hole repair. The archived source must be restored, rather
than treated as an unused or withdrawn lemma. Compiling it reproduces the import error:
`Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation` conflicts with the already
loaded upstream declaration `AlgebraicGeometry.affineDerivedCohomologyModules`.

The adopted source library already contains the intended complete identity-edge proof.
A source diff confirms that, beyond the header and canonical factorization import, its
only differences are six explicit sheaf-universe annotations. The existing DAG attachment
still named the quarantined duplicate instead of that canonical provider. Reusing the
provider resolves the collision and prevents a second declaration of the same theorem.
The original proof dependencies and unit route remain valid. Zero rings, zero complexes,
unbounded complexes, arbitrary integer degrees and arbitrary supplied comparisons remain
covered; no mathematical hypothesis or conclusion changes.

The library search found the exact upstream theorem. The required Lean Finder search
returned unrelated identity/cohomology lemmas; Loogle did not index the project theorem,
and the remote grep service returned no hit. Local `rg` and direct source comparison
identified and verified the exact match. `tools/downstream.py --allow-missing --uses`
reports no downstream source modules for the quarantined path; active and quarantined
source searches likewise find no importer of that path. The actual theorem consumer
already imports the upstream provider, and its unchanged proof was checked in scratch
through the restored path. No consumer adaptation or new node is required.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
