# HomologicalComplex₂.tensorBicomplexMap

## Reason

Complete the direct Mathlib reuse requested by upstream review #1424. The
object is already a compatibility abbreviation of Mathlib's bifunctor object.
The map now directly abbreviates the uncurried functor's map, without the
`dsimp%` elaboration wrapper. This removes the DSimpPercent tactic dependency.
The compatibility names remain under the duplicate-definition rule in stage 3.

## Old

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  dsimp% only [Functor.uncurry] (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)
```

## New

```lean
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.TensorBicomplex | Y3 | Direct Mathlib map alias. |
| Sheaf.Algebra.Homology.TensorResolutionColumnCokernelIso | unclaimed | Forced: add Functor.uncurry_obj_map to the final simp only list. |
| Sheaf.Algebra.Homology.TensorResolutionRowCokernelIso | unclaimed | Forced: add Functor.uncurry_obj_map to the final simp only list. |
| Sheaf.Algebra.Category.ModuleCat.TorSymmetry | unclaimed | Compiles unchanged against the new map. |
| Sheaf.Algebra.Homology.FlatResolutionTorComparison | unclaimed | Direct importer; compiles unchanged. |

The original column module fails at line 108 with an unsolved naturality goal:
its right side retains `((Functor.uncurry.obj ...).map (a,b)).f p |>.f 0`.
The original row module fails at line 151: `change` cannot identify the
unsimplified uncurried map with `a.f 0 ⊗ₘ b.f q`. Each adaptation adds exactly
one Mathlib simp lemma to the failing proof; no signatures or visibility change.
The original modules compile against the baseline and the adapted modules
compile against the delivered definition (also checked by deliver3.py).

Scratch checks establish by `rfl` equality with the previously normalized map
composition, and prove the component formula for arbitrary degrees and both
zero-map cases. Thus definitions used in targets retain their mathematical
meaning; this evidence is supplied for their reopened definition review. No
target statement or unit route changes. The node's proof plan now records the
explicit use of Mathlib's uncurrying API in the two callers.

## Status

landed 20261013T234526-L-2168881 2026-10-13 (merge of deliver/Y3/Sheaf.Algebra.Homology.TensorBicomplex)
