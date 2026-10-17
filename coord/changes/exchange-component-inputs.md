# Cartesian exchange component inputs

## Reason

Separate the geometric component inputs from the categorical natural-transformation assembly,
without duplicating the existing exchange definition or changing any original public signature.

## Old

The item had two whole-theorem inverse-existence sorries. The retained failed attempt supplied
an unconnected duplicate exchange construction and two component claims about that duplicate.

## New

Add `boundedConstructibleOpenImmersionLowerShriekBaseChange_app_mono` in `ExchangeMono` and
`boundedConstructibleOpenImmersionLowerShriekBaseChange_app_section` in `ExchangeSection`.
Each accepts a natural transformation and an equality to the explicit existing exchange formula.
The item's original exchange supplies this equality by reflexivity, in its proof only.
Two old holes close and two strictly componentwise holes remain. No definition data is chosen
from an existence theorem, and no existing statement or definition changes meaning.

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | C3 | Two proof-only imports and two theorem proof replacements; all signatures and definition bodies unchanged. |

The two added declarations have no pre-existing downstream users. No existing public definition,
statement, visibility or public import changes, so downstream statements and Challenge targets
keep their exact meanings. No forced consumer adaptation is needed.

## Status

landed 20261017T032449-L-1749299 2026-10-17 (merge of deliver/C3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs)
