# AlgebraicGeometry.Scheme.Modules.scalarExtCup_inverseImage

## Reason

Restore the quarantined module assigned in coord/rework.tsv. Its archived source
publicly imports a withdrawn empty module. The unmodified archive fails compilation
at line 26 with `Unknown identifier Field`, with the compiler explaining that Field
is imported privately. The scalar sheaf definitions used in the public statement
now belong to the adopted upstream module. Replacing the public import restores
that interface without changing any declaration or proof.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The theorem signature and complete proof are verbatim from the quarantine archive.
No definitions, instances, target signatures, or adopted source files are changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage | C3 | Restored from quarantine; public statement elaborates using the canonical upstream definitions. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | quarantined, unclaimed | Direct proof consumer; its call to scalarExtCup_inverseImage has identical type. Its own stale public import is an independent quarantine repair; no adaptation is forced by this change. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | quarantined, unclaimed | Transitive consumer through ScalarCupPullbackNaturality; no declaration changes. Its own stale public import is an independent quarantine repair. |

| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | quarantined, unclaimed | Transitive consumer through ScalarCupPullbackCoefficientNaturality; unchanged statement and proof. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined, unclaimed | Transitive consumer through PicardKunnethQcohFunctoriality; unchanged statement and proof. |

Source searches cover lean/ and quarantine/: no live Lean module imports the item,
and ScalarCupPullbackNaturality is the only direct archived importer and theorem
user. tools/downstream.py cannot list this module while it is absent from lean/;
the quarantine sources were therefore checked explicitly. The original and new
theorem texts are identical. The canonical upstream operation node already points
to the new imported module; the item's statement and proof dependency nodes remain
correct and need no edits. No target definition changes, so no semantic target
review is reopened by this import repair.

## Status

landed 20261020T211643-L-3484174 2026-10-20 (merge of deliver/C3/Sheaf.AlgebraicGeometry.ScalarExtCupInverseImage)
