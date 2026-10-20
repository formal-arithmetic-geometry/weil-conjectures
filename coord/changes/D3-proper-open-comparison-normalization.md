# AlgebraicGeometry.ProEtale.StrictTower.properOpenComparisonNormalization

## Reason

The target proof needs one independent structural result combining invertibility of the
explicit restriction map, its cartesian normalization, and equality of its open adjunct
with `gamma`. The result is left as a named split theorem with its own DAG node. The two
proved helper theorems are private because they are implementation lemmas used only by
the target module; this keeps the public interface unchanged apart from the split node.

## Old

The item module contained only the target theorem and its original definitions.

## New

A private proved `properOpenNormalization` and `properOpenFiniteNormalization`, plus the
public split theorem `properOpenComparisonNormalization`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProperOpenTowerComparison | D3 | Target proof uses the private helpers and the split structural theorem. |

## Status

landed 20261020T235548-L-1189515 2026-10-20 (merge of deliver/D3/Sheaf.Paper.ProperOpenTowerComparison)
