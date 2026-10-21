# AlgebraicGeometry.Scheme.Modules.picard_kunneth_functoriality

## Reason

Restore the complete quarantined module recorded by coord/rework.tsv. Its former
public import of the retired Sheaf scalar-operations module now imports an empty
module. The original archive fails with unknown identifiers scalarCohomology,
scalarCohomologyMap and externalCup; Lean explicitly requests the canonical
upstream public import. Import the upstream operations publicly because the
existing theorem statement uses these operations. Preserve the archived theorem
signature, proof, visibility, attributes and all other imports verbatim.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The retired module contains only `module` and a withdrawal comment.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

This is the operations module already attached to
`def-sc-field-linear-module-cohomology-operations`. No definitions, target
statements, coefficient comparisons or mathematical dependencies change. No
source-library file is edited. The proof remains scalar cup pullback/coefficient
naturality followed by the two projection-square identities.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | K2 | Restored with canonical public operations import; clean compile and standard axioms only. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined; unclaimed | Sole archived direct importer and theorem user; same theorem signature and call. Its independent stale operations import remains a separate rework. |

`tools/downstream.py Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality
--uses picard_kunneth_functoriality` reports an unknown module because the source
is quarantined. A source scan of lean/ and quarantine/ finds exactly the direct
consumer above. Its application `picard_kunneth_functoriality k X Y f g F G`
is unchanged. A validation-only sandbox copy of that archive with its own retired
operations import replaced by the canonical upstream public import compiles
against the restored artifact in 3.8 seconds. This validation copy is not delivered;
no consumer or archive is removed or adapted by this packet. The unit route and
all DAG dependencies remain unchanged.

## Status

landed 20261021T004832-L-1792455 2026-10-21 (merge of deliver/K2/Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality)
