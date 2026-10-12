# coherentIntegralFiltration_of_shortExact

## Reason

The proof reuses the existing private subobject-filtration realization theorem via
`import all Sheaf.CategoryTheory.FiniteFiltrationRefinement` and the coherent
kernel/cokernel closure theorem. Three copied private declarations were removed.
The direct Extensions import was removed because it is available through the all-import.
This changes only the proof body and proof-only imports; the public theorem signature is unchanged.

## Old

`theorem coherentIntegralFiltration_of_shortExact (X : Scheme.{u}) [IsLocallyNoetherian X]
(S : ShortComplex X.Modules) (hS : S.ShortExact) (h₁ : RingedSpace.IsCoherent X.toRingedSpace S.X₁)
(h₂ : RingedSpace.IsCoherent X.toRingedSpace S.X₂) (h₃ : RingedSpace.IsCoherent X.toRingedSpace S.X₃)
(hA : HasCoherentIntegralFiltration S.X₁) (hB : HasCoherentIntegralFiltration S.X₃) :
HasCoherentIntegralFiltration S.X₂`

## New

The same signature, with a complete proof body.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes | unclaimed | recompiles against the proved theorem |

## Status

landed 20261012T212210-L-1098217 2026-10-12 (merge of deliver/R2/Sheaf.AlgebraicGeometry.CoherentIntegralFiltrationExtension)
