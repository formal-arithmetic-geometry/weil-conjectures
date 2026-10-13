# Repair duplicate Picard cokernel declaration

## Reason

The canonical upstream declaration is `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient`; this module now provides that name and retains the old name as a compatibility alias.

## Old

`Scheme.Hom.pic_proper_ntorsion_coker` was the primary declaration in this module.

## New

The proved declaration uses the canonical upstream name. The old declaration remains a compatibility alias with the same signature and proof. Return H10 is repaired by removing its deprecation attribute, avoiding a warning in the direct importer.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | P1 | continues using compatibility alias |

## Status

landed 20261013T215613-L-901712 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker)
