# Sheaf.Paper.AdicPurityObjects imports

## Reason

After proving the three theorem holes, remove the unused direct imports of
`IntegralOperationsPreserveConstructible` and `NormalizedDVREffectivity`.
The actual definitions and theorem signatures need the two retained public imports.
The coefficient-unit proof uses Mathlib declarations already available from the retained imports.
No existing declaration signature or definition is changed. The finite-Tor proof
projects the existing integral predicate and needs no effectivity theorem.

The import removal changes the public import list, so it is submitted for independent
review. `IntegralOperationsPreserveConstructible` remains publicly reachable through
`AdicPurityTwistReduction`, `AdicPurityFiniteTensor`, `AdicPurityRootComparisons`,
`FiniteCoefficientSmoothPurity`, and `DerivedPullbackTensorHom`.
There is no assertion that `NormalizedDVREffectivity` remains publicly reachable.
The existing consumers must not rely on its accidental re-export.

## Old

```lean
public import Sheaf.Paper.AdicPurityTwistReduction
public import Sheaf.Paper.ExceptionalFiniteSupportRealization
public import Sheaf.Paper.IntegralOperationsPreserveConstructible
public import Sheaf.Paper.NormalizedDVREffectivity
```

## New

```lean
public import Sheaf.Paper.AdicPurityTwistReduction
public import Sheaf.Paper.ExceptionalFiniteSupportRealization
```

## Users

`tools/downstream.py Sheaf.Paper.AdicPurityObjects` lists exactly these three consumers.
No consumer is adapted or included in the delivery. Their statements, definitions,
and public visibility are unchanged.
All three unchanged consumer sources compile against the edited module in import
order using `lcompile.py --all`: exceptional reduction in 16.5 seconds, source
reduction in 17.8 seconds, and reconstruction in 11.7 seconds, with no warnings.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Unchanged direct consumer. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Unchanged direct consumer. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Unchanged transitive consumer. |

## Status

landed 20261019T112612-L-3960963 2026-10-19 (merge of deliver/W9/Sheaf.Paper.AdicPurityObjects)
