# ModuleSupportProperOverBase proof import

## Reason
The annihilation theorem module is used only by the proof body. Its import must be plain so downstream modules do not receive a proof-only dependency.

## Old
`public import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`

## New
`import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase | M2 | proof retains the import; downstream interface no longer re-exports it |

| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.CoherentSupportProperHigherDirectImage | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.CoherentFormalModule | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | not claimed by this delivery | no signature change; no use of the annihilation theorem; tensor pullback where used is imported separately |
| Sheaf.Paper.FiniteStructureAlgebraLift | not claimed by this delivery | no signature change; compiles against the delivered module with the public re-export removed |
| Sheaf.Paper.FiniteStructureProperSupport | not claimed by this delivery | no signature change; compiles against the delivered module with the public re-export removed |

## Status
landed 20261012T135253-L-1677435 2026-10-12 (merge of deliver/M2/Sheaf.AlgebraicGeometry.ModuleSupportProperOverBase)
