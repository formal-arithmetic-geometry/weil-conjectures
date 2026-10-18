# strictly henselian constant sections naturality interface
## Reason
The delivery adds the public split theorem and a linter option required for its proof scaffold.
## Old
No declaration or linter option.
## New
`nonempty_strictlyHenselian_constant_sections_natural_iso` and `set_option linter.style.haveILetI false`.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero | F6 | uses the split theorem in the main proof |
## Status
landed 20261018T062752-L-649601 2026-10-18 (merge of deliver/F6/Sheaf.AlgebraicGeometry.StrictlyHenselianConstantHZero)
