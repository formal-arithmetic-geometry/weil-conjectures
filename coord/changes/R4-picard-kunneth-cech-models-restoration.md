# AlgebraicGeometry.Scheme.Modules.picard_kunneth_cech_models

## Reason

Restore the quarantined module assigned in coord/rework.tsv (cluster restore,
2026-10-20). The archive has a complete proof and zero sorry bodies. Its public
FieldLinearModuleCohomologyOperations import points to the withdrawn Sheaf module,
which now has no declarations. The original fails in its public statement with
unknown identifiers scalarCohomology and externalCup; Lean explicitly requests the
WeilConjectures public import. Import the adopted source module directly.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The remainder of the old module is preserved verbatim from
quarantine/Sheaf/AlgebraicGeometry/PicardKunnethCechModels.lean.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The theorem signature, visibility, proof, constructions and all other imports are
unchanged. No definition or mathematical statement changes, including the targets.
The existing node attachment and three proof dependencies remain valid unchanged.

## Users

Searches of lean/ and quarantine/ find one direct importer/textual consumer, also
quarantined. Scanning actual DAG statement/proof dependency fields finds the same
single parent. tools/downstream.py does not index this absent item (unknown module),
so these source and DAG checks include the quarantined parent explicitly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardKunnethCechModels | R4 | Restored with the corrected public source import; compiles in 3.8 s. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohIso | unclaimed | Existing theorem consumer preserved. Its entire archived proof compiles against the restored item in a scratch probe after migrating its own obsolete public field-linear import to WeilConjectures. No consumer file is delivered or withdrawn. |

The consumer probe compiled in 4.6 s. The item's proof compiled in the same overlay
in 5.4 s. Both axiom prints contain only propext, Classical.choice, Quot.sound and
sorryAx inherited from existing proof dependencies; this restoration adds no holes
and no custom axioms.

## Status

landed 20261020T230829-L-618112 2026-10-20 (merge of deliver/R4/Sheaf.AlgebraicGeometry.PicardKunnethCechModels)
