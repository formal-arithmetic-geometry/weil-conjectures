# AlgebraicGeometry.diagonal_baseChange_upperShriek

## Reason

Restore the quarantined module listed in coord/rework.tsv. The archived source publicly
imports the withdrawn Sheaf.AlgebraicGeometry.DerivedPullback, which exports no declarations.
The theorem statement uses derivedPullback, so its defining source module must be public.
Fill the existing theorem hole by specializing proper-flat right-adjoint base change and
using the already-proved derived structure-sheaf pullback isomorphism.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackStructureSheaf
```

The existing theorem signature, universes, hypotheses and conclusion are unchanged.
No definition is changed. The source-library boundary is preserved; no source module is edited.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | C2 | Restored archive; current definition publicly visible; theorem hole filled. |

`tools/downstream.py --allow-missing --uses diagonal_baseChange_upperShriek` reports
zero current downstream modules. A search of lean/, quarantine/ and dag/nodes/ found
no distinct Lean consumer of this declaration. The quarantined local-derived-categories
variant has its own theorem and imports, and DiagonalPushforwardStructure uses that
variant. The existing DAG attachment is retained. No target meaning or consumer statement
changes, and no consumer adaptation is required.

## Status

landed 20261025T180512-L-3996404 2026-10-25 (merge of deliver/C2/Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek)
