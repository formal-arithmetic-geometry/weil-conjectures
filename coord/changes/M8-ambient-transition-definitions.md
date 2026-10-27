# AlgebraicGeometry.Scheme.pbcAmbientCompleteKaroubiTransition

## Reason

The two eager transition aliases expanded the entire Karoubi extension in large
coherence types. Keep their names folded during elaboration. The full support
module compiled in 51.8 seconds with these ordinary definitions before the further
raw-category normalization, and in 36.8 seconds with the complete repair set.

## Old

```lean
abbrev pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcAmbientCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W F)).obj
      (pbcAmbientCompleteRawTransition l Ω W h)

abbrev pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
```

## New

```lean
def pbcAmbientCompleteKaroubiTransition (h : E ≤ F) :
    pbcAmbientCompleteKaroubiStage l Ω W E ⥤ pbcAmbientCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcAmbientCompleteStage l Ω W E) (pbcAmbientCompleteStage l Ω W F)).obj
      (pbcAmbientCompleteRawTransition l Ω W h)

def pbcConstructibleCompleteKaroubiTransition (h : E ≤ F) :
    pbcConstructibleCompleteKaroubiStage l Ω W E ⥤
      pbcConstructibleCompleteKaroubiStage l Ω W F :=
  (Idempotents.functorExtension₂
    (pbcConstructibleCompleteStage l Ω W E) (pbcConstructibleCompleteStage l Ω W F)).obj
    (pbcScalarExtension l Ω W hDim.out hInv.out h)
```

Each complete body and signature is otherwise verbatim, so equality to the old
body is rfl. Both remain Mathlib's supported Karoubi extension of the same raw
transition. Objects, projectors, arrows, scalar actions, systems, associators and
coherence statements are unchanged. All original public coherence proofs remain
complete. This definition repair is submitted for independent target-meaning review.

## Users

The declaration-use queries find only AmbientCompleteCoefficientCategories.
All downstream modules below are checked without source changes. All support
modules were unclaimed when checked on 2026-10-22.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbientCompleteCoefficientCategories | unclaimed | keep exactly the same two transitions as ordinary definitions |
| Sheaf.Paper.FiniteStageKaroubiExtension | unclaimed | unchanged consumer |
| Sheaf.Paper.FiniteStageRationalExchangeData | unclaimed | separate clause naming has its own record |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalOperationCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalRawOperationCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalRawSquareExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.RationalSquareExchangeCoherence | unclaimed | unchanged consumer |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | M8 | same completed coefficient systems and comparisons in the new proof |

The private additivity-proof adaptation in the same module is recorded in
M8-coherent-descent-explicit-objects.md. No other source lines change.
Final successful compilation is recorded in report.md.

## Status

landed 20261022T040208-L-2831428 2026-10-22 (merge of deliver/M8/Sheaf.Paper.QbarCoefficientSmoothBaseChange)
