# Polynomial.completeLocalFormalFibres

## Reason

The queue assigns this module to retirement. The adopted source module
`WeilConjectures.RingTheory.PolynomialCompleteLocalFormalFibres` already proves the
identical regularity theorem as
`Polynomial.isRegular_algebraMap_adicCompletion_localization`. The Sheaf file is a
duplicate wrapper and has no current Lean importers. The DAG node is repointed to the
canonical source declaration in this delivery.

## Old

`Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres` declared
`Polynomial.completeLocalFormalFibres` with the regular completion-map statement for a
Noetherian complete local ring and maximal polynomial ideal over the maximal ideal.

## New

The duplicate Sheaf module is withdrawn. The node names
`Polynomial.isRegular_algebraMap_adicCompletion_localization` in
`WeilConjectures.RingTheory.PolynomialCompleteLocalFormalFibres`, whose signature and
meaning are identical. The source module remains unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| none | unclaimed | no current module imports the withdrawn Sheaf path; source-root consumers use the canonical upstream declaration |

## Status

landed 20261020T233138-L-898967 2026-10-20 (merge of deliver/F5/Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres)
