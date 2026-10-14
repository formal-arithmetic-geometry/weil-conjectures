# HomologicalComplex₂.tensorBicomplexMap

## Reason

Repair reviewer X-9c100 point 2. The returned local `let F` body changes
reduction and breaks existing importers. Restore exactly the requested
`dsimp% only [Functor.uncurry]` body, which simplifies the canonical Mathlib
uncurried bifunctor map at elaboration time. No importer adaptations are needed.

## Old

The returned delivery used:

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  let F := Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
    (.down ℕ) (.down ℕ)
  (Functor.uncurry.obj F).map (X := (P, Q)) (Y := (P', Q')) (a, b)
```

The repository baseline uses the unsimplified canonical expression:

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)
```

## New

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  dsimp% only [Functor.uncurry] (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.TorSymmetry | unclaimed | Original source retained. |
| Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso | unclaimed | Original source retained. |
| Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso | unclaimed | Original source retained. |

This restores the reviewer-requested reduction of the same canonical map;
no target statement or mathematical definition changes meaning.

## Status

landed 20261014T084700-L-88935 2026-10-14 (merge of deliver/F2/Sheaf.Algebra.Homology.TensorBicomplex)
