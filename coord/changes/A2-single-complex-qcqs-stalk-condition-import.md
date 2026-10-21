# AlgebraicGeometry.singleComplexBaseChange_homology_mono public import

## Reason

Restore the module quarantined by the upstream sync to `a762b776d`. The archive
named by `coord/rework.tsv` contains a complete proof with zero holes, but its
public statement refers to `SingleComplexBaseChange.StalkCondition` through the
withdrawn, empty Sheaf module. The provider is now the adopted source module.
Compiling the unchanged archive reproduces the recorded unknown-identifier error;
Lean explicitly recommends publicly importing the adopted provider.

Repair of return `e482bfdb8c3`: the current rework row and A2 claim were checked.
The item is absent from the live Lean tree. Restore its current quarantine
source at the original path and deliver against the freshly fetched `sheaf-dag`;
preserve the archive and the node's existing Lean attachment and dependencies.

Change that public import. Every other line, including the theorem signature,
visibility, docstring and proof, is identical to the current quarantine archive.
The signature also equals the current node's `lean.statement` verbatim. All six
declared proof dependencies and the unit route are retained. No definition,
target statement or source-library file changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
```

## Users

The source-only downstream check is run with `--allow-missing`, because the item
is quarantined. A separate search of both `lean/` and `quarantine/` finds exactly
one direct importer and caller: the quarantined standard-flat single-base-change
monomorphism module. Its archived source is validated without modifications in
`scratchpad/`, outside the delivery packet. No consumer signature changes.
The repaired item compiles in 3.0 seconds (4.0 seconds in the consumer-validation
set), and its unchanged consumer compiles in 21.0 seconds. A separate importing
probe reports only `propext`,
`Classical.choice` and `Quot.sound` as the theorem's axioms. The import-direction
check permits the new public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono | A2 | Restore with the correct public provider; signature and proof retained. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeMono | unclaimed in shared claim snapshot | Quarantined direct caller; unchanged signature and proof. |

The existing node remains attached to this restored module. No withdrawal or
replacement argument is proposed. There are no new nodes or proof holes.

## Status

landed 20261021T125932-L-2459334 2026-10-21 (merge of deliver/A2/Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono)
