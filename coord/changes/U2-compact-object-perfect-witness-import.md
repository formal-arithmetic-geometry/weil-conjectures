# AlgebraicGeometry.compactObject_perfect_witness

## Reason

Restore the quarantined item recorded in coord/rework.tsv and replace its obsolete
compact-object statement import with the adopted source module. The Sheaf compact-object
module is now withdrawn and exports no declarations. The existing proof-only import of
DerivedQCohCompactRepresentatives imports the source compact-object declaration privately,
which cannot supply IsCompactObject to this module's public theorem statement.
No theorem signature, definition, proof body, target meaning, or DAG dependency changes.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

Every other line is preserved verbatim from the current quarantine archive.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness | U2 | Restored; public signature vocabulary supplied by the current defining module. |

Source searches of lean/ and quarantine/ find no importers or declaration users.
The DAG parent lem-sc-proper-perfect-preserves-compact still cites this result;
its statement and dependencies remain valid. The item is restored, not withdrawn.
No consumer requires adaptation. No source-library file changes.

A separate importing probe successfully checks both the theorem and IsCompactObject.
Its axiom print reports exactly propext, Classical.choice and Quot.sound.
The repaired module and importing probe compile together through lcompile.py --all.

## Status

landed 20261020T150710-L-2575387 2026-10-20 (merge of deliver/U2/Sheaf.AlgebraicGeometry.CompactObjectPerfectWitness)
