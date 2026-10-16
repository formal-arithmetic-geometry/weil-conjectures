# Integral constructible kernel proof commands

## Reason

The interface checker flags the added proof commands in
`Sheaf.Paper.IntegralConstructibleKernels`: a second universe, variables for generic
abelian categories, namespace openings, local preservation instances, and a scoped
heartbeat setting. These support private, proved helpers for the kernel argument.
This record documents that conservative command-level flag. The existing public theorem's
signature, visibility and public imports are unchanged; no existing definition is changed.

## Old

The module had `universe u`, its category-theory openings and the coefficient variables,
and a single public theorem `integralConstructible_kernels` with an unproved body.

## New

The module additionally declares `universe v`, opens namespaces used by private helpers,
and uses scoped generic category variables, local instances and proof options. All newly
added declarations in this module other than the unchanged public theorem are private
and proved. Its public theorem is proved by the pivot induction and presentation argument.
The new module `Sheaf.Paper.IntegralMatrixPivotCover` has one public theorem and its own
new DAG node. The added imports are proof-only. No downstream adaptation is needed.

## Users

The following are the complete downstream closure at the time of this check. Only
`Sheaf.Paper.IntegralConstructibleSerre` mentions the existing theorem directly; its
statement and use remain valid. No downstream source file is changed.

| Module | Holder | Effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralConstructibleKernels | H2 | Private proof helpers and proof commands |
| Sheaf.Paper.IntegralMatrixPivotCover | H2, new local module | New pivot statement |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | A4 | No source adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No source adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No source adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Existing theorem signature identical |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No source adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No source adaptation |
| TargetsCheck | unclaimed | No source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No source adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No source adaptation |

## Status

landed 20261016T021741-L-1028349 2026-10-16 (merge of deliver/H2/Sheaf.Paper.IntegralConstructibleKernels)
