# CategoryTheory.MonoidalClosed.evaluationBidualComparisonTransport

## Reason

Remove the unused public import of Sheaf.Paper.DualityPairing. The declarations use the
existing MonoidalClosed internal Hom and toIhomIhom constructions. The pairing theorem is
not needed by the statements or their proofs. All declaration signatures and definitions
remain unchanged, and no target meaning changes.

## Old

```lean
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Sheaf.Paper.DualityPairing
```

## New

```lean
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.EvaluationBidualComparisonTransport
--uses evaluationBidualComparisonTransport` reports zero downstream modules and only the
declaration's own module as a textual user. No consumer needs adaptation. Unfinished DAG
parents retain the same public declarations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.EvaluationBidualComparisonTransport | U1 | Unused import removed; signatures unchanged. |

## Status

landed 20261022T145653-L-2039775 2026-10-22 (merge of deliver/U1/Sheaf.CategoryTheory.EvaluationBidualComparisonTransport)
