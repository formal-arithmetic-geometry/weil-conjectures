# Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy public import

## Reason

The proof and all public declarations in `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`
use `Sheaf.Algebra.Homology.ModuleHomComplex`, `Mathlib.Algebra.Homology.Single`, and the
cochain HomComplex API. They do not use any declaration from
`Mathlib.Algebra.Homology.DerivedCategory.Basic`. Removing that unused public import keeps
the module interface minimal while preserving all declarations and signatures.

## Old

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
```

## New

The line is removed. The module retains these public imports:

```lean
public import Sheaf.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.Single
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace` | unclaimed | Direct importer; compiled successfully against the reduced interface. |
| `Sheaf.CategoryTheory.DerivedCategory.FrameDualMate` | unclaimed | Direct importer; compiled successfully against the reduced interface. |
| `Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws` | unclaimed | Transitive importer through `ChainSupertrace`; its public `PerfectCategoricalTrace` import supplies the derived-category interface. |
| `Sheaf.Paper.CondensedPointSupertrace` | unclaimed | Downstream user; no declaration or import change required. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Downstream user; no declaration or import change required. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Downstream user; retains its own required import of `Mathlib.Algebra.Homology.DerivedCategory.Basic`. |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | unclaimed | Downstream user; no declaration or import change required. |
| `Sheaf.Paper.PointRealizationCoefficientComparison` | unclaimed | Downstream user; no declaration or import change required. |

## Status

landed 20261019T144020-L-2348842 2026-10-19 (merge of deliver/R1/Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy)
