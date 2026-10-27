# CategoryTheory.ExactAdjointTorTests import interface

## Reason

The abstract Tor-test theorem does not use any open-immersion normalization data.
Its existing universe-generalized localized adjunction uses only the exact-derived
functor API and the degreewise adjunction API. Replace the unrelated public import
with those two precise public imports. All declaration signatures and definition
bodies are unchanged; the previously unfinished theorem is now proved.

## Old

```lean
public import Sheaf.SixFunctors.OpenTensorNormalizationData
```

## New

```lean
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
```

## Users

`python3 tools/downstream.py Sheaf.CategoryTheory.DerivedCategory.ExactAdjointTorTests`
reports zero downstream modules. A direct search of both Lean roots agrees.
No declaration, instance, or definition in a consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DerivedCategory.ExactAdjointTorTests | A7 | Remove unused open-normalization re-export; retain exact localized adjunction with precise imports. |

No target statement uses a changed definition: no definition changes here.

## Status

landed 20261023T134738-L-2748432 2026-10-23 (merge of deliver/A7/Sheaf.CategoryTheory.DerivedCategory.ExactAdjointTorTests)
