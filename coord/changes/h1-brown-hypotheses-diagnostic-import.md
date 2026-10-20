# h1-brown-hypotheses-diagnostic-import

## Reason

The diagnostic packet adds a private proof import of the new structural
intermediate module to `Sheaf.SixFunctorsBasics.BrownHypotheses`. This exposes no
new declaration through the original item and is required for the proved
structural result to compile in the item module.

## Old

`Sheaf.SixFunctorsBasics.BrownHypotheses` had no import of
`Sheaf.SixFunctorsBasics.BrownHypothesesStructural`.

## New

`Sheaf.SixFunctorsBasics.BrownHypotheses` imports
`Sheaf.SixFunctorsBasics.BrownHypothesesStructural` privately. The new module
provides `CategoryTheory.brownHypotheses_structural`, a proved ambient
intermediate theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | H1 | imports the structural theorem for the diagnostic packet |
| `Sheaf.Paper.LocalizingExceptionalAdjoint` | unclaimed | unchanged; it continues to import the original item |

## Status

landed 20261020T051346-L-1651141 2026-10-20 (merge of deliver/H1/Sheaf.SixFunctorsBasics.BrownHypotheses)
