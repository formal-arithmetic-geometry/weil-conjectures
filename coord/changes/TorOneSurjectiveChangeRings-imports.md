# Sheaf.Algebra.TorOneSurjectiveChangeRings imports

## Reason

The second reader narrowed imports to the declarations used in the unchanged
public theorem signature and proof. `Mathlib.CategoryTheory.Monoidal.Tor` was
used only transitively for projective resolutions; `ModuleCat.Projective` only
for `Module.Free`. Import their smaller defining modules publicly instead.
The `exact₀` lemma is needed only in the proof and is imported privately from
`Mathlib.CategoryTheory.Abelian.Projective.Resolution`.
No definition, statement, visibility, or target meaning changes.

## Old

```lean
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
```

## New

```lean
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.FlatOfLocalCriterionBaseChange | Q1 | Sole direct importer; imports this module privately. Its original source compiles unchanged against the revised module in a scratch overlay. Its signature and meaning are unchanged. |

`tools/downstream.py Sheaf.Algebra.TorOneSurjectiveChangeRings --direct`
identified this sole direct importer. Transitive downstream modules cannot see
these imports through its private import. No adaptation is needed or delivered.

## Status

landed 20261013T100131-L-2488677 2026-10-13 (merge of deliver/T2/Sheaf.Algebra.TorOneSurjectiveChangeRings)
