# Restricted affine natural proof local transparency

## Reason

Keep expensive derived cohomology and inverse-image constructions folded during
elaboration of the target proof. Without these local attributes, compilation
sometimes exceeds 60 seconds. The attributes are local to the namespace in this
file and do not affect any imported declaration's definition or importer-visible
interface. Preflight conservatively treats the attribute command as an interface
change and requests this record.

## Old

No local transparency attributes.

## New

```lean
attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rawAffineRestrictedCohomology rightDerivedGlobalSections DerivedCategory.Q
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | N1 | Local proof elaboration keeps the definitions folded; all signatures unchanged. |
| Sheaf.AlgebraicGeometry.AbelianRawCoconeComplexPresentation | unclaimed | No effect; local attributes are not exported, and the theorem signature is identical. |

No downstream module is adapted; no original module fails because of these local
attributes. No definition or target meaning changes. No target review is reopened.

## Status

landed 20261013T082357-L-1640805 2026-10-13 (merge of deliver/N1/Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural)
