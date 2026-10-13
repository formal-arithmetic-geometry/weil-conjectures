# HomologicalComplex₂.tensorBicomplexMap

## Reason

Upstream review #1424 asks that tensor bicomplex objects and maps use Mathlib.
The object is already a compatibility abbreviation of the canonical bifunctor.
Replace the remaining written-out map composition by the map of Mathlib's
`Functor.uncurry.obj` of that bifunctor. Normalize only `Functor.uncurry` at elaboration using `dsimp% only` to retain
the existing simplification API. Keep the compatibility name, as required
by the project's rule for duplicate definitions. The result type is inferred
from Mathlib's map rather than restated. It is definitionally identical to the
old type; no binder, universe, visibility or mathematical statement changes.

## Old

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') : tensorBicomplex P Q ⟶ tensorBicomplex P' Q' :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).map a).app Q ≫
    ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P').map b
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
| Sheaf.Algebra.Homology.TensorBicomplex | P2 | Alias Mathlib's uncurried map directly. |
| Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso | unclaimed | Compiled unchanged against the delivered alias. |
| Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso | unclaimed | Compiled unchanged against the delivered alias. |
| Sheaf.Algebra.Category.ModuleCat.TorSymmetry | unclaimed | Compiled unchanged against the delivered alias. |
| Sheaf.Algebra.Homology.FlatResolutionTorComparison | unclaimed | Does not mention tensorBicomplexMap; compiled unchanged as an additional direct-importer check. |

No consumer is adapted. The elaborated body of the abbreviation reduces the
uncurrying map to the previous composition, retaining every consumer signature
and proof unchanged. Currying is a public import used by the data alias;
DSimpPercent is an ordinary import used only during elaboration.

Scratch Lean checks prove by `rfl` that the new map equals the old composition,
check its original type, and prove its components are `a.f p ⊗ₘ b.f q` for arbitrary
p and q, including degree zero and zero maps. Thus no definition appearing in a
target changes meaning; this evidence is supplied for the reopened definition
review. No target statement changes. The unit route and proof dependencies stay.

## Status

landed 20261013T222408-L-1224751 2026-10-13 (merge of deliver/P2/Sheaf.Algebra.Homology.TensorBicomplex)
