# integral_cohomological_adic_criterion

## Reason

Stage-3 proof of the existing theorem. Preflight classifies additional section commands
as changing what other modules see and requires this record. No theorem signature,
public import, existing instance, definition or target statement changes. The added
commands make exact-functor and module-category comparisons elaborate predictably.

The proof adds private helper definitions and private proved helper instances for its
exact scalar realization, exact local restriction, slice derived categories and the
lifted coefficient domain. They introduce no axiom or hole. The original
`integralCriterionWEquals` instance is unchanged. No public definition refers to a
private helper; the public theorem's proof may use them.

The unit-route import `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit` is
retained, as requested by preflight. Its coefficient identification is not needed in
the direct comparison of the two local-model predicates, but the unit's route remains.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory
```

## New

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
```

The public theorem signature is verbatim unchanged; its sole `sorry` is replaced by a
complete proof. Existing declaration docstrings and public imports are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.IntegralCohomologicalAdicCriterion --uses
integral_cohomological_adic_criterion integralCriterionWEquals` lists the following
14 downstream modules. Neither existing declaration name occurs in a downstream
statement or proof (the name search finds only this module itself). No consumer's
mathematical statement changes because all existing signatures and definitions remain
verbatim. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | {'who': 'B9', 't': 1792587701.100595, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralConstantModelHeart` | {'who': 'T3', 't': 1792589926.4555614, 'since': '2026-10-21T13:38:46Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralConstructibleHeart` | {'who': 'T9', 't': 1792587701.486529, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralHeartDualizable` | unclaimed | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralHeartLocalModel` | {'who': 'W7', 't': 1792587701.6025865, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralHeartRealizationExact` | unclaimed | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralHeartResidueDual` | unclaimed | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralModels` | {'who': 'U1', 't': 1792587700.8717752, 'since': '2026-10-21T13:01:40Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralStratumHomFormula` | {'who': 'K6', 't': 1792587701.2161849, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralTensorPullback` | {'who': 'C5', 't': 1792593374.0433772, 'since': '2026-10-21T14:36:14Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.IntegralWindowCoproductComparison` | unclaimed | Unchanged statements and definitions; no adaptation. |
| `Sheaf.Paper.RationalLocalizedHom` | {'who': 'C3', 't': 1792593374.0208073, 'since': '2026-10-21T14:36:14Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralExtHomContinuity` | {'who': 'A7', 't': 1792587701.0366917, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | {'who': 'W8', 't': 1792587701.6179917, 'since': '2026-10-21T13:01:41Z'} | Unchanged statements and definitions; no adaptation. |

## Status

landed 20261021T160059-L-3498537 2026-10-21 (merge of deliver/J4/Sheaf.Paper.IntegralCohomologicalAdicCriterion)
