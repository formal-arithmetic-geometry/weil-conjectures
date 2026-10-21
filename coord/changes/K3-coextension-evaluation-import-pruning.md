# Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula imports

## Reason

The evaluation formula is a theorem about internal module objects in an arbitrary
symmetric monoidal closed category. It uses no ring presheaves or sheafification.
Remove the unused public RingPresheaf import and the redundant private
Adjunction.Basic import; Adjunction.Unique supplies the adjunction proof API.
All existing declaration signatures, definitions, attributes and docstrings stay
unchanged. No target statement or its mathematical meaning changes.

## Old

```lean
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
```

## New

```lean
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.CategoryTheory.Adjunction.Unique
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula --uses
CategoryTheory.Mod.coextendScalarsIsoComapInv_formula` reports zero downstream
modules and the item's own declaration as its sole textual use. A source search
of both library roots and the target files also finds no current importers.
The DAG parent and unit route still need this theorem: this delivery preserves
its module, Lean attachment and dependencies, and withdraws no module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula | K3 | Complete proof; unused imports removed. |

## Status

landed 20261021T111230-L-61299 2026-10-21 (merge of deliver/K3/Sheaf.CategoryTheory.CoextensionIsoEvaluationFormula)
