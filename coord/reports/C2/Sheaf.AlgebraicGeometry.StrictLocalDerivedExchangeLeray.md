## What changed

Maintenance completed the metadata repair requested by reviewer C-4f264 for
returned delivery 4f26466b7704f7d754632158631643c32d54ff76 at 2026-10-20T17:08:06Z. Seven nodes now use the existing adopted
WeilConjectures providers. Their lean.statement values are exactly those of the
returned delivery; the other lean fields are preserved except module and file.
Every non-lean node field, all dependencies, and all quarantine archives are
unchanged. No Lean library source was changed.

| Node | Provider |
| --- | --- |
| `lem-weil-pbc-strict-local-complex-sections-mate` | `WeilConjectures.AlgebraicGeometry.StrictLocalComplexSectionsMate` |
| `lem-weil-pbc-strict-local-derived-exchange-global-sections` | `WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeGlobalSections` |
| `lem-weil-pbc-strict-local-derived-exchange-leray` | `WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeLeray` |
| `lem-weil-pbc-strict-local-derived-mate-sections-factorization` | `WeilConjectures.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization` |
| `lem-weil-pbc-strict-local-injective-source-derived-restriction` | `WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction` |
| `lem-weil-pbc-strict-local-injective-source-restriction` | `WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceRestriction` |
| `lem-weil-pbc-strict-local-injective-source-sections` | `WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceSections` |

The seven obsolete rework rows were closed by rebinding, not by restoring or
proving the duplicates. The original rows and return are preserved in
coord/changes/C2-strict-local-derived-exchange-maintenance-20261021.md. The rejected delivery is archived at refs/superseded/C2/Sheaf.AlgebraicGeometry.StrictLocalDerivedExchangeLeray/4f26466b7704f7d754632158631643c32d54ff76; its live delivery
ref and the completed C2 claim are removed. Only this item's return is closed.

## Proved and sorry left

No new proof, no holes added, no holes closed, and no split statements. The seven
adopted files contain no sorry and match the source in sheaf-verified 4075ceb2e3739398321829e59398e43211d5f9b8.
A single scratch file applied all seven declarations at the exact returned
signatures and printed their axioms, using tools/lean_file.sh with a 60-second
limit. It passed with no warnings. Every axiom list contains only propext,
Classical.choice, and Quot.sound. The check and source hashes are preserved in
local/maintenance/C2-StrictLocal-1792515590/.

## No longer needed

The seven duplicate Sheaf providers remain absent from lean/. No live library
source imports them. Their quarantined archives remain byte-for-byte intact for
historical evidence. All seven mathematical nodes and their dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The returned delivery restored seven duplicate declarations already supplied by
WeilConjectures. Importing both providers causes an environment collision. The
reviewer correctly required rebinding without those duplicate sources.

deliver3.py's item-source check and tools/stage3_delivery.py's changed-item check
cannot deliver this metadata-only correction. The worker brief also forbids
listing an already-absent quarantined source in deleted.txt just to pass the gate.
Repeated dispatch therefore reproduced the same failure without changing its
cause. The maintenance repair corrects the authoritative records directly under
the merge lock. It changes no delivery or landing tool and claims no new proof.

This returned item is completed. A stale worker should refresh server records
and stop work on the old return; do not restore the duplicate files or push the
rejected delivery again. General support for reviewer-ordered metadata rebinding
in the protected delivery path remains a launcher-owner follow-up.
