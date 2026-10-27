# Matrix.rowMinorIdeal_stable_invariance

## Reason

Remove the unused public import of FreeModule.Basic. The statement and real
rowMinorIdeal construction use submodules of a function space and linear
projections, supplied by the retained public imports. They do not use a
Module.Free instance or any declaration from FreeModule.Basic.

## Old

```lean
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Pi
import Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions
```

## New

```lean
public import Sheaf.LinearAlgebra.Matrix.MinorIdeal
public import Mathlib.LinearAlgebra.Pi
import Sheaf.LinearAlgebra.Matrix.MinorIdealInclusions
```

## Users

`tools/downstream.py Sheaf.LinearAlgebra.Matrix.RowMinorIdealStableInvariance`
reports zero downstream modules. A text search over both Lean roots finds no
importer and no use of either public declaration outside its own module.
No statement or definition changes; the public signatures and construction
are identical. The DAG parent remains an unfinished consumer, and its route
is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.LinearAlgebra.Matrix.RowMinorIdealStableInvariance | T8 | Compiles with the retained imports; all public declarations unchanged. |

## Status

landed 20261023T124515-L-1413125 2026-10-23 (merge of deliver/T8/Sheaf.LinearAlgebra.Matrix.RowMinorIdealStableInvariance)
