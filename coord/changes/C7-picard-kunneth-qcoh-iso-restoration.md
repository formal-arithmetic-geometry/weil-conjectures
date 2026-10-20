# AlgebraicGeometry.Scheme.Modules.picard_kunneth_iso_exists

## Reason

Restore the module from the exact quarantine path in coord/rework.tsv. The archived
module contains a complete proof and zero sorry bodies, but publicly imports the
withdrawn Sheaf field-linear cohomology operations module. That module is now empty.
The declarations used by the statement live in the adopted WeilConjectures module.
Import that source module publicly, so scalarCohomology, externalCupCoefficients and
externalCup are available in the public statement.

The archived source was compiled and fails with unknown identifiers
scalarCohomology and externalCup. Lean explicitly requests the adopted public
import above. With that sole change, the complete theorem compiles in 5.4 seconds.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

All remaining text is the archived module at
quarantine/Sheaf/AlgebraicGeometry/PicardKunnethQcohIso.lean.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The theorem signature, visibility, proof and all other imports remain verbatim.
The mathematical statement, all definitions and the targets are unchanged. The
existing DAG attachment, proof, proof_deps and proof_origin still describe the proof.
Both declared proof dependencies remain necessary: the geometric Cech-model
comparison and the algebraic natural-degree tensor Kunneth theorem.

## Users

tools/downstream.py reports this absent quarantined module as unknown. Searches of
both lean/ and quarantine/ find one direct importer and declaration consumer, the
quarantined PicardKunnethQcoh. Scanning every DAG node's stmt_deps, proof_deps and
proof-step uses finds precisely its node as the parent. Its isomorphism clause
applies the restored theorem with exactly the same arguments and conclusion.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | C7 | Restored; public import corrected. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | unclaimed | Quarantined parent preserved; theorem interface unchanged. Its own obsolete public import requires the same separate restoration repair. No consumer edit in this packet. |

No upstream source module is edited. No declaration, module or DAG attachment is
withdrawn. The quarantine archive stays intact.

The compiler initially lacked the recently restored Cech-model object's published
artifact. Its exact unchanged current source was checked separately (10.2 seconds),
then compiled with the item using the supported sandbox compile set. The temporary
dependency source was removed afterwards and is not part of the delivery.
An importer probe compiles the parent's unchanged isomorphism clause in 10.8
seconds by applying this theorem. The axiom print lists propext, Classical.choice,
Quot.sound and inherited sorryAx. No new holes or axioms are added.

## Status

landed 20261020T233110-L-893528 2026-10-20 (merge of deliver/C7/Sheaf.AlgebraicGeometry.PicardKunnethQcohIso)
