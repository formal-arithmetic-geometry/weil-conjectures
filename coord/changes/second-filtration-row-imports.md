# SecondFiltrationRowCohomology public imports

## Reason

The theorem constructs its page-zero complex and concrete positive pages directly.
It does not use the general existential filtered-complex spectral-sequence theorem.
Replace the public import of that theorem's module by the two modules that the
unchanged statement actually needs. This prunes the general construction and
positive-pages assembly from this item's import closure. No declaration signature,
visibility, definition, or target meaning changes.

## Old

```lean
public import Sheaf.CategoryTheory.FilteredComplexSpectralSequence
import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.DoubleComplexTotal
```

## New

```lean
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.CategoryTheory.FilteredComplexGradedHomology
import Sheaf.CategoryTheory.FilteredComplexPageHomology
import Sheaf.CategoryTheory.SecondFiltrationSignedFirstPage
```

The existing public import of CartanEilenbergPresentation is retained. The single
existing public theorem keeps its complete original signature and visibility.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CartanEilenbergRowPages | unclaimed | The only direct importer already explicitly publicly imports FilteredComplexSpectralSequence. It uses the unchanged secondFiltration_row_cohomology theorem. No adaptation is required. |

Transitive users keep the same interface through CartanEilenbergRowPages, which
independently imports the removed module. No other module directly imports the
changed module. No forced adaptations are delivered. The unchanged direct importer was compiled
against the sandbox overlay and passed cleanly.

## Status

landed 20261012T202235-L-702851 2026-10-12 (merge of deliver/E1/Sheaf.CategoryTheory.SecondFiltrationRowCohomology)
