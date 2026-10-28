# WeilConjectures.coefficientDerivedSectionsCoreData

## Reason

Fill the proof and move proved private implementation helpers to two new modules to meet the 60-second compile limit. The preflight flags command-level changes, including a local namespace opener; no existing public signature, definition, instance or public import changes.

## Old

```lean
theorem coefficientDerivedSectionsCoreData (R : CoefficientDerivedSystemReduction l E W) (hF : CoefficientFiniteTensorNormalization l E W R) : Nonempty (CoefficientDerivedSectionsCoreData l E W R)
```

## New

```lean
theorem coefficientDerivedSectionsCoreData (R : CoefficientDerivedSystemReduction l E W) (hF : CoefficientFiniteTensorNormalization l E W R) : Nonempty (CoefficientDerivedSectionsCoreData l E W R)
```

The proof is complete. Both new modules contain only proved private helpers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientDerivedSectionsCore | not adapted | Original compiles unchanged against delivery |
| Sheaf.Paper.CoefficientDerivedSectionsCoreEquations | not adapted | Original compiles unchanged against delivery |

Both direct importers passed the delivery compatibility compile. No forced adaptations.

## Status

landed 20261028T055742-L-804508 2026-10-28 (merge of deliver/R3/Sheaf.Paper.CoefficientDerivedSectionsCoreData)
