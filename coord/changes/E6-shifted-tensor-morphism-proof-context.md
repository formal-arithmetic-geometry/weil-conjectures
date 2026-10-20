# SheafOfModules.shiftedTensorMorphismCalculus proof context

## Reason

Preflight detects the added namespace opening and universe declaration as a change to
commands visible to importers. These commands support private generic proof helpers;
no existing declaration signature, definition body, instance, or public import changes.
The three theorem proofs are completed without additional hypotheses or weakened
conclusions. No mathematical target meaning changes and no consumer needs adaptation.

The transparency option avoids expanding concrete tensor and localization data during
elaboration. The new irreducibility attributes belong only to the private constructions
`totalComplexSwap` and `totalSwapNatIso`. A fully proved private component lemma
for `totalSwapNatIso` supplies the formula used by the symmetry proof, avoiding
unfolding the construction at each specialization. No attribute on an existing declaration is changed or exported.

## Old

```lean
set_option warn.sorry false
set_option backward.isDefEq.respectTransparency false
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
universe u v w

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory

universe u₁ v₁ u₂ v₂ w₁ w₂
```

The added universes occur only in private generic helpers. Existing declarations retain
their original universe parameters and signatures. The existing definition bodies are
verbatim; the command changes affect proof elaboration in this module only.

The returned head `cbd99f5e59` was refused because the source hole census read
`warn.sorry` before the first declaration as an unattributed hole. The redundant
warning-suppression command is now removed. This changes diagnostics only; all four
remaining proof holes stay in their original named public theorems.

## Users

`tools/downstream.py Sheaf.Paper.ShiftedTensorMorphismCalculus` reports the following
21 transitive importers. The item itself is included as well. Claim holders were read
from the coordination claim records. No consumer is edited. The corresponding
`--uses shiftedTensorMorphismCalculus` search finds the item itself; the interfaces
used by its parents retain their names, visibility, statements and mathematical meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ShiftedTensorMorphismCalculus | E6 | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Same public signatures and definitions; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Same public signatures and definitions; no adaptation. |

## Status

landed 20261020T221136-L-4148659 2026-10-20 (merge of deliver/E6/Sheaf.Paper.ShiftedTensorMorphismCalculus)
