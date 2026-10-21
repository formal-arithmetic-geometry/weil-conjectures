# CategoryTheory.coefficientDiagram_regularScalars

## Reason

The proof concerns abstract monoid objects and uses neither ring presheaves nor a
new application of free-monoidal coherence. Remove the two unused imports. The
public ring-presheaf import removal is recorded because it reduces re-exported API.

## Old

```lean
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
```

## New

```lean
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
```

All existing declaration signatures, attributes and definition bodies are unchanged.
A declaration-local `linter.unusedSectionVars` option preserves the existing braided
parameters of `coefficientDiagram_isMonHom`; the proof does not use them. The proved
private helper `map_leftScalar` has no braided assumptions.
No target statement or definition changes meaning.

## Users

`tools/downstream.py` reports zero downstream modules. Text search of both library
roots finds no current importer. DAG parents still require this item; it is retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ModuleObjects.CoefficientDiagramRegularScalars | P2 | Three proofs completed; unused imports removed; declaration interfaces preserved. |

## Status

landed 20261021T120438-L-3896355 2026-10-21 (merge of deliver/P2/Sheaf.CategoryTheory.ModuleObjects.CoefficientDiagramRegularScalars)
