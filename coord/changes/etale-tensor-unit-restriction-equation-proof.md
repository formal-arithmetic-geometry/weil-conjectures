# AlgebraicGeometry.Scheme.Modules.etaleTensorUnitRestriction_equation

## Reason

The proof adds private helper declarations and local proof configuration to the
existing module. The delivery tool records these as an interface delta even though
they are private and therefore unavailable to importers. The public theorem
signature and public imports are unchanged.

## Old

The module contained the public theorem
`AlgebraicGeometry.Scheme.Modules.etaleTensorUnitRestriction_equation` with proof
`by sorry`, and no helper declarations.

## New

The same public theorem is proved. Five helper theorems are added as `private`:
`tensorStructureMap_comp`, `topRestriction_id`,
`structureMapSectionsOfAdjunction`, `tensorStructureMap_sections`, and
`tensorStructureMap_restriction`. They are implementation details and are not
exported by the module.

## Users

| User | Holder | Reason |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleTensorUnitSectionsNatural | unclaimed | Direct importer; compiles unchanged; private/local proof commands are not exported. |

## Status

landed 20261012T223358-L-1634127 2026-10-12 (merge of deliver/A3/Sheaf.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation)
