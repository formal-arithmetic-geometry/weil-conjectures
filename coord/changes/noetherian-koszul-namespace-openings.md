# Sheaf.RingTheory.NoetherianKoszulAugmentationProZero namespace openings

## Reason

The proof uses zero-object lemmas and opposite-category notation. Preflight requests a
change record for the extra namespace openings. All original public imports, the target
signature, and declaration visibility are unchanged. The auxiliary constructions are private.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

## Users

`tools/downstream.py Sheaf.RingTheory.NoetherianKoszulAugmentationProZero --uses
ExteriorAlgebra.noetherian_koszul_augmentation_pro_zero` lists two downstream modules and
only the item's own declaration as a textual user. Namespace openings affect elaboration
within this file; they do not alter the meaning of any target or any importing module.
No consumer adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.NoetherianKoszulAugmentationProZero | Q2 | proof can use limits and opposite notation |
| Sheaf.Paper.AdicCompletionReduction | no claim in shared snapshot | unchanged imports and statement |
| Sheaf.Paper.KoszulQuotientLimit | no claim in shared snapshot | unchanged imports and statement |

## Status

landed 20261018T091410-L-3258148 2026-10-18 (merge of deliver/Q2/Sheaf.RingTheory.NoetherianKoszulAugmentationProZero)
