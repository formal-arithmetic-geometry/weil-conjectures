# CategoryTheory.Functor.coefficientCompositionModuleComparison

## Reason

The generic module transport comparison uses module objects and adjunction mates only.
It does not use ring presheaves. Remove the unused public import of the ring-presheaf
module, so that this generic theorem does not acquire unrelated dependencies. The
single-file compiler checks both declarations against the remaining imports.

## Old

```lean
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Adjunction.Mates
```

## New

```lean
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Adjunction.Mates
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ModuleObjects.CoefficientCompositionComparison | H4 | Remove unused public ring-presheaf import; statements and definition unchanged. |

`tools/downstream.py Sheaf.CategoryTheory.ModuleObjects.CoefficientCompositionComparison
--uses coefficientCompositionModuleComparison restrictedModuleTransport` lists no
importers or downstream declaration users. No consumer adaptation is necessary.
The existing DAG parents may use this theorem when their proofs are completed;
its statement and its required public types are unchanged. No target definition
or statement changes, and no source-library declaration or import is modified.

## Status

landed 20261022T143824-L-1403373 2026-10-22 (merge of deliver/H4/Sheaf.CategoryTheory.ModuleObjects.CoefficientCompositionComparison)
