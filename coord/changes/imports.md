# imports
## Reason
The concrete coefficient-system module is proof-only for the target and must be a private import.
## Old
`public import Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientSystem`
## New
`public import Sheaf.AlgebraicGeometry.RawAffineRestrictedCohomology`
`import Sheaf.AlgebraicGeometry.RestrictedAffineCoefficientSystem`
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RestrictedAffineComplexSystemNatural | F1 | unchanged public interface |
## Status
landed 20261013T164047-L-1667806 2026-10-13 (merge of deliver/E3/Sheaf.AlgebraicGeometry.RestrictedAffineNaturalCoefficientSystem)
