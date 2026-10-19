# AlgebraicGeometry.TotalTensorHomotopyRight

## Reason

The proof-only import `WeilConjectures.Mathlib.Algebra.Homology.Bifunctor` introduces
a name-resolution collision for the previously unqualified `Functor.postcompose₂`.
Qualify it as `CategoryTheory.Functor.postcompose₂`. This names the same functor;
the signature, construction, and mathematical meaning of the definition are unchanged.
The module is also converted to the required `module` / `public section` convention.
Its statements retain their required public projection import, while the proof-only
imports listed in report.md are removed. No target signature or definition changes.

## Old

```lean
noncomputable def TotalTensorHomotopyRight :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  ((Functor.postcompose₂.obj (L.mapHomotopyCategory (.up ℤ))).obj
    ((((whiskeringLeft₂ _).obj (𝟭 (HomotopyCategory C (.up ℤ)))).obj
      (R.mapHomotopyCategory (.up ℤ))).obj
      (F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))))
```

## New

```lean
noncomputable def TotalTensorHomotopyRight :
    (HomotopyCategory C (.up ℤ) ⥤ HomotopyCategory D (.up ℤ) ⥤ HomotopyCategory D (.up ℤ)) :=
  ((CategoryTheory.Functor.postcompose₂.obj (L.mapHomotopyCategory (.up ℤ))).obj
    ((((whiskeringLeft₂ _).obj (𝟭 (HomotopyCategory C (.up ℤ)))).obj
      (R.mapHomotopyCategory (.up ℤ))).obj
      (F.bifunctorMapHomotopyCategory (.up ℤ) (.up ℤ) (.up ℤ))))
```

## Users

`tools/downstream.py Sheaf.Paper.EtaleSumTensorTotalization
--uses AlgebraicGeometry.TotalTensorHomotopyRight` reports zero downstream modules
and one module using the name, the item itself (two occurrences).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleSumTensorTotalization | S2 | Name qualification only; existing signatures and meaning unchanged; compiled cleanly in 35.5 seconds against the current remote build. |

## Status

landed 20261019T005419-L-2766252 2026-10-19 (merge of deliver/S2/Sheaf.Paper.EtaleSumTensorTotalization)
