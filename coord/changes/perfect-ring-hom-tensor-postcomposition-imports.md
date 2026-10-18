# CategoryTheory.perfectRingHom_tensorDual_postcomposition

## Reason

The component calculation needs the definitions of the signed degree condition, not the
existence or invertibility theorem for degree maps. Narrow its public import accordingly;
the theorem's signature and meaning are unchanged. The added proof-only import supplies
naturality of the specified tensor-sheafification comparison. No definitions are changed,
and no target statement needs renewed mathematical review.

## Old

```lean
public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.PerfectRingDualTermFlat
```

## New

```lean
public import Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeCondition
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
```

All existing declaration signatures are preserved. The sole existing theorem changes
only from `by sorry` to a complete proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition | T4 | Own module; narrower public import and proved theorem. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | unclaimed in shared claims | Immediate consumer imports PerfectRingHomTensorDegrees publicly itself; its use of the unchanged theorem is unaffected. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso | unclaimed in shared claims | Transitive consumer; the differential module still re-exports PerfectRingHomTensorDegrees. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed in shared claims | Transitive consumer; unchanged theorem and preserved inherited interface. |
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unclaimed in shared claims | Transitive consumer; unchanged theorem and preserved inherited interface. |

`tools/downstream.py Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition`
listed exactly these four downstream modules. No consumer adaptation is needed.

## Status

landed 20261018T071226-L-1678539 2026-10-18 (merge of deliver/T4/Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition)
