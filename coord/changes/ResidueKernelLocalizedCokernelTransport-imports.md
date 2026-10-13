# ResidueKernelLocalizedCokernelTransport proof-only import pruning

## Reason

`Mathlib.RingTheory.Localization.BaseChange` supplies declarations used only in the
proof of `localized_range_quotient_extendScalars_aux`. The public theorem signatures
already obtain their required definitions from the other public imports, so this import
is made private to the module.

## Old

```lean
public import Mathlib.RingTheory.Localization.BaseChange
```

## New

```lean
import Mathlib.RingTheory.Localization.BaseChange
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernel | unclaimed | unchanged signatures; its existing imports provide all declarations it uses |
| Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernelTransport | X3 | proof compiles with the plain import |

No target statement or definition changes, and no adaptation is needed.

## Status

landed 20261013T215617-L-903137 2026-10-13 (merge of deliver/X3/Sheaf.Algebra.Homology.ResidueKernelLocalizedCokernelTransport)
