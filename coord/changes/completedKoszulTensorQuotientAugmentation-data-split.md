# completedKoszulTensorQuotientAugmentation data split

## Reason

The strict tower, quotient unit, and summand definitions are shared by the existence
and uniqueness split statements. They are moved to a public data module so the split
modules do not import the theorem module cyclically. Their declarations and meanings
are unchanged and remain publicly re-exported by the theorem module.

## Old

`Sheaf.Paper.CompletedKoszulTensorQuotientAugmentation` publicly imported
`Sheaf.Paper.KoszulReconstructionModels` and declared
`completedKoszulTensorTower`, `completedQuotientTensorUnit`, and
`completedKoszulTensorSummand` in that module.

## New

`Sheaf.Paper.CompletedKoszulTensorQuotientAugmentationData` publicly imports
`Sheaf.Paper.KoszulReconstructionModels` and declares the same three definitions.
`Sheaf.Paper.CompletedKoszulTensorQuotientAugmentation` publicly imports the new data
module through the existence module, preserving the public names and signatures.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedKoszulQuotientRoosAugmentation | unclaimed | public names remain available through the theorem module |
| Sheaf.Paper.CompletedKoszulTensorQuotientConeProZero | V3 | public names remain available through the theorem module |
| Sheaf.Paper.CompletedKoszulTensorQuotientAugmentation | Y2 | theorem imports the split components |

## Status

landed 20261027T021420-L-2772620 2026-10-27 (merge of deliver/Y2/Sheaf.Paper.CompletedKoszulTensorQuotientAugmentation)
