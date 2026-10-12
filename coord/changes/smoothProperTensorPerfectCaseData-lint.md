# smoothProper_tensor_perfect_case_data lint option
## Reason
The proof leaves theorem binders unused because the split-off quasi-coherent assertion supplies the data independently of the Tor hypothesis. A theorem-local linter option suppresses these proof-only warnings.
## Old
No `linter.unusedVariables` option.
## New
`set_option linter.unusedVariables false in` immediately before the theorem docstring.
## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData | E3 | proof lint configuration only |
## Status
landed 20261012T202237-L-703603 2026-10-12 (merge of deliver/E3/Sheaf.AlgebraicGeometry.SmoothProperTensorPerfectCaseData)
