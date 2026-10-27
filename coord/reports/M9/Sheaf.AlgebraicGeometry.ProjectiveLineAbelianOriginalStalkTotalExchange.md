## What changed

Complete the explicit retirement assignment for
Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange. Withdraw its
proved smallModel adapter and migrate its only direct consumer,
Sheaf.AlgebraicGeometry.ProjectiveLineOriginalStalkTotalCohomologyExchange, to the
adopted abelian theorem. Move the exact small/full-model isomorphism transport into
that consumer. Its complete signature, original docstring, public imports and
coefficient/naturality proof remain unchanged. Reattach the abelian DAG node to the
adopted canonical theorem and update both proof plans to match the executable proof.
No source-library file changes.

Change record: coord/changes/M9-retire-projective-line-abelian-original-stalk.md.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. No decomposition or new statements.
The item was already proved; this is the listed retirement repair.
Etale.projectiveLine_originalStalk_totalCohomologyExchange_smallModel remains fully
proved with its exact original statement. No sorry remains in any delivered Lean
file. The adopted Etale.projectiveLine_abelian_originalStalk_totalExchange and its
complete proof are preserved. No assertion is made that all transitive dependencies
are sorry-free; the server preflight reports their axiom closure.

## No longer needed

Module Sheaf.AlgebraicGeometry.ProjectiveLineAbelianOriginalStalkTotalExchange and
its public theorem Etale.projectiveLine_abelian_originalStalk_totalExchange_smallModel
are withdrawn. Remove that private import from the sole direct consumer and import
the adopted canonical implementation instead. This prunes one wrapper module.
No mathematical node is pruned: lem-weil-pbc-p1-abelian-original-stalk-total-exchange
now names the adopted canonical theorem, and its parent still uses it. The small/full
comparison dependency moves from the abelian wrapper to the consuming proof.
ProjectiveSpace.isPullback_map, the abelian localization theorem and the strict-local
abelian total-exchange theorem remain needed by the adopted proof. No claim is made
that their modules are unnecessary. The transitive small-model strict-local caller
needs no edit. The unit's statement and all realized proof steps remain.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open hole, but the current queue explicitly
assigns retirement and the current item has zero holes. The adopted theorem uses
strictLocalization; the old wrapper uses strictHenselizationScheme, so a name-only
import migration would be ill-typed. Preserve the complete canonical-colimit
transport in the caller before removing the wrapper. The old abelian node pointed
to the adapter; it now points to the existing adopted theorem realizing the same
abstract mathematical statement. The parent proof plan now records the transport
explicitly. Searches through msearch.py found no shorter Mathlib replacement;
repository search found the already-proved adopted theorem.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
