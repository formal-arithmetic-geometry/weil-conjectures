# AlgebraicGeometry.exists_positiveCopyGradedQuotient public imports

## Reason

Remove unused public proof dependencies. The remaining public imports already
provide the module-sum and categorical coproduct APIs used by the signatures. All existing
public definitions, theorem signatures and attributes remain unchanged.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient | W7 | Own proof and imports updated; signatures unchanged. |

`tools/downstream.py` reports zero downstream Lean modules for the item and only
the item itself as a textual user of each of its three public declarations.
No consumer adaptations are needed. The DAG parent remains attached to the
unchanged theorem, and target meanings do not change.

## Status

landed 20261024T021940-L-2880529 2026-10-24 (merge of deliver/W7/Sheaf.AlgebraicGeometry.PositiveCopyGradedQuotient)
