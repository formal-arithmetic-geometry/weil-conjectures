# Retire the cohomology image compatibility abbreviation

## Reason

The assigned RETIRE item removes `Sheaf.CategoryTheory.FilteredCohomologyImage` in favor
of `WeilConjectures.CategoryTheory.FilteredCohomologyImage`. The Sheaf-only name is already
an abbreviation for the upstream construction, so the migration preserves the objects
and statements by definitional equality. No upstream file or target statement is changed.

## Old

The compatibility module publicly imported the upstream twin and added:

```lean
noncomputable abbrev cohomologyImage (n : ℤ) : DecreasingFiltration (K.homology n) :=
  L.homologyFiltration n
```

Consumers imported the compatibility module and wrote `L.cohomologyImage n`.

## New

The compatibility module is withdrawn through `deleted.txt`. Each live consumer imports
`WeilConjectures.CategoryTheory.FilteredCohomologyImage` and writes
`L.homologyFiltration n` directly. The theorem name `cohomologyImage_isFinite` and the
names of all cycle and graded presentation theorems stay unchanged. No theorem proof is
replaced by an admission. Existing imports of other Sheaf modules are retained.

The finiteness node already points at the upstream twin; its note now records complete
retirement of the compatibility module. The four affected presentation nodes' `lean.statement`
fields are updated to use the canonical name. Their mathematical statements and proof
routes are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence` | unclaimed | Replace the import and five filtration expressions. |
| `Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap` | unclaimed | Replace the import and six filtration expressions. |
| `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized` | unclaimed | Replace the import and five filtration expressions. |
| `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation` | unclaimed | Replace the import and one filtration expression. |
| `Sheaf.CategoryTheory.FilteredStableSubquotient` | unclaimed | Replace the import and one filtration expression. |
| `Sheaf.CategoryTheory.FilteredPageTwoComparison` | unclaimed | Replace the import and fifteen references, including the explicit unfolding. |
| `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` | unclaimed | Inventory consumer; current source has no reference, compiled unchanged. |
| `Sheaf.CategoryTheory.FilteredStationaryCycleComparison` | retired by J1 during this session | Current empty module is preserved and compiled unchanged; its consumers already import the upstream twin. |

## Status

landed 20261021T005752-L-1890573 2026-10-21 (merge of deliver/T1/Sheaf.CategoryTheory.FilteredCohomologyImage)

All live consumer adaptations are supplied together with the compatibility-module
withdrawal. The independent reviewer and maintainer's global build verify the packet.
