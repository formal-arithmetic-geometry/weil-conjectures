# AlgebraicGeometry.Scheme.ProEt.finite_cover_refinement

## Reason

The returned delivery repeated a private theorem from the existing module
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`.
Importing that module alone does not make its private theorem accessible.
Expose the existing theorem in place, remove the duplicate theorem and its
proof from `ProEtaleAbelianEvaluationColimits`, and import and use the original.
The source module is unclaimed (no claim file on 2026-10-16).
The unclaimed-module exception in the worker brief authorizes this change.

## Old

```lean
private theorem finite_cover_refinement (X : Scheme.{u}) (W : X.ProEt)
    [IsAffine W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ ∀ i, S (f i)
```

## New

```lean
theorem finite_cover_refinement (X : Scheme.{u}) (W : X.ProEt)
    [IsAffine W.left] (S : Sieve W) (hS : S ∈ topology X W) :
    ∃ (I : Type (u + 1)) (_ : Finite I) (V : I → X.ProEt) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ topology X W ∧ ∀ i, S (f i)
```

The source module changes only the `private` keyword. Its theorem body,
binders, docstring, imports and all other declarations are unchanged. The
helper is exported by the existing `@[expose] public section`.
The theorem states a proposition, so exposing it changes no construction or
target meaning. No existing public signature changes. The new DAG attachment
records this existing result; it introduces no duplicate declaration.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
--uses finite_cover_refinement` found one existing user: the source module
itself. The helper was private, so no downstream module could refer to it.
The 45 transitive importers retain their existing interfaces and need no edit.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits | unclaimed | Expose the existing helper; its internal call remains unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits | G2, new delivery module | Remove duplicate private helper and import and use the existing public theorem. |

This is an authorized change to an unclaimed module, not a forced adaptation
of a module held by another group. No other existing Lean file is adapted.

## Status

landed 20261016T040116-L-2417209 2026-10-16 (merge of deliver/G2/Sheaf.Paper.CondensedQcqsPushforwardLocalComparison)
