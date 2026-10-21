# Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison imports

## Reason

The direct public import of `Sheaf.CategoryTheory.SiteCoveringAxioms` is unused.
`Sheaf.CategoryTheory.BraidedSheafTensorGenerators`, which remains publicly imported,
already publicly imports that module. Removing the duplicate edge preserves all
transitively exported declarations and instances.

## Old

```lean
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.BraidedSheafTensorGenerators
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
```

## New

```lean
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.BraidedSheafTensorGenerators
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison`
reports zero downstream modules. No consumer needs adaptation. The item's public
signatures and definition bodies are unchanged; its parent DAG nodes can use the
proved comparison with the same types. No target meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison | F3 | Remove duplicate import |

## Status

landed 20261021T061056-L-1696739 2026-10-21 (merge of deliver/F3/Sheaf.CategoryTheory.SheafPushforwardGeneratorComparison)
