# Algebra.exists_finitePresentation_local_approximation_closedFibre

## Reason

Remove the unused public import `Mathlib.RingTheory.Localization.Algebra` from
`Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation`, as required by pruning.
The proof uses the localization API in `Mathlib.RingTheory.Localization.Basic`
and `Mathlib.RingTheory.Localization.Ideal`, already provided by the retained
imports. This does not alter the theorem signature or any definition.

## Old

```lean
public import Mathlib.RingTheory.Localization.Algebra
```

## New

The import is removed. All other existing imports remain, and the proof adds:

```lean
import Mathlib.RingTheory.PrincipalIdealDomain
```

## Users

`python3 tools/downstream.py Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation
--uses Algebra.exists_finitePresentation_local_approximation_closedFibre` reports
zero downstream modules and only the declaration's own occurrence in its module.
A repository-wide search also finds the node name in the proof docstring of
`Sheaf.AlgebraicGeometry.FibrewiseFlatnessCriterion`; its unfinished proof remains
able to import this theorem with precisely the same statement. No adaptation is
needed, and no target definition or statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation | C9 | Complete proof, unchanged signature; unused import removed. |

## Status

landed 20261023T123419-L-1185246 2026-10-23 (merge of deliver/C9/Sheaf.RingTheory.FiniteTypeLocalClosedFibreApproximation)
