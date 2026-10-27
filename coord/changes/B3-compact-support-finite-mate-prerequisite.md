# WeilConjectures.sfQcqsCompactSupport_finiteMates prerequisites

## Reason

Delivery preflight exposed the cycle from the new realization through finite
comparison and finite mates to the whole integral coefficient-comparison node,
which already depends on this item. The Lean proof of finite mates uses the
specific openComparison_isIso helper from that bundled module, alongside the
already separate comparison_factorization. It does not invoke the overall
integralCoefficientComparison theorem. The new node attaches that existing named
helper without changing or duplicating its Lean declaration.

## Old

The exact former proof dependency list was:

```json
[
 "lem-pur-compact-support-comparison-factorization",
 "lem-pur-compact-support-integral-coefficient-comparison",
 "lem-sf-complete-direct-image-reduction",
 "lem-weil-pbc-integral-coefficient-presentation-comparison",
 "lem-weil-pbc-ring-sheaf-change-adjunction"
]
```

The last proof step cited the entire
lem-pur-compact-support-integral-coefficient-comparison for openComparison_isIso.
No Lean signature or body is changed by this metadata repair.

## New

The exact new proof dependency list is:

```json
[
 "lem-sf-complete-direct-image-reduction",
 "lem-weil-pbc-ring-sheaf-change-adjunction",
 "lem-weil-pbc-integral-coefficient-presentation-comparison",
 "lem-pur-compact-support-comparison-factorization",
 "lem-pur-open-coefficient-comparison-isomorphism"
]
```

The last proof step now cites lem-pur-open-coefficient-comparison-isomorphism,
which states exactly the existing openComparison_isIso helper. Its normalized
geometric open comparison and scalar-adjunction transport are independent of
the overall integral coefficient comparison. A graph reachability check finds
no path from any of the four new nodes back to the assigned item.
The node statement, Lean attachment, module signatures, instances, attributes,
public imports and code of finite mates all stay unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.QcqsCompactSupportFiniteMates` | unclaimed in current claim records (last delivery X6) | Only its node prerequisite is made precise; its Lean proof and statement stay unchanged. |
| `Sheaf.Paper.QcqsCompactSupportFiniteComparison` | unclaimed in current claim records | Its existing finite-mate prerequisite retains exactly the same theorem and module. |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | unchanged existing module | The new node attaches the already existing openComparison_isIso; no source edit or new hole. |
| `Sheaf.Paper.CompactSupportProjectionRealization` | B3 (new) | Its finite-comparison prerequisite now has an acyclic declaration-specific route. |

There is no consumer adaptation, signature change or recompilation requirement
from this metadata-only correction. The four delivered Lean files have already
compiled and completed the delivery axiom probes against these same existing
Lean prerequisites.

## Status

landed 20261027T012808-L-2331698 2026-10-27 (merge of deliver/B3/Sheaf.Paper.CompactSupportScalarProjectionIdentification)
