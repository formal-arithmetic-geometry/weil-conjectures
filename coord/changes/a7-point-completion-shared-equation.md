# WeilConjectures.PointEvaluationCompletion.betaCompletionEquation

## Reason

The sections-balancing construction and the normalization theorem use the same
strict chain square. Give that square one construction-owned definition,
`WeilConjectures.PointSectionsCompletionEquation`, and make the existing predicate
refer to it. This avoids repeatedly converting two large presentations of the
same Roos and tensor equation. The private proved lemma `beta_completion_chain`
converts it definitionally back to the original equation, with the original
`chainChi` and `unitCompletion`. Its proof is the supplied proof itself, so Lean
checks that the old and new propositions are definitionally identical.

No binder, universe, hypothesis, map, or conclusion of the normalization theorem
changes. The equation still applies to arbitrary rho and beta; no balancing
hypothesis was added to the definition. The construction-owned predicate is a
real proposition definition, independent of the new unproved existence theorem.
The combining proof stays in the item module. The new public import is required
because an existing public definition now uses the construction-owned predicate.

## Old

```lean
@[no_expose] def betaCompletionEquation
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj (total D l E C.obj J.obj)) : Prop :=
  beta ≫ (pointIntegralComplexSections D l E).map (chainChi D l E C.obj J.obj rho) =
    unitCompletion D l E hl S canonical P C J eta
```

## New

```lean
@[no_expose] def betaCompletionEquation
    (hl : l ≠ D.p) (S : PointIntegralTensorData D l hl E)
    (canonical : PointIntegralTensorCanonical D l hl E S)
    (P : CochainComplex (ModuleCat.{u + 1} (R l E)) ℤ)
    (C J : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (rho : (integralOperationsTensorTowerFunctor l E (Spec (.of D.k))).obj
      (C.obj, J.obj) ≅ (tower D l E).obj (total D l E C.obj J.obj))
    (eta : P ⟶ (pointIntegralComplexSections D l E).obj C.obj)
    (beta : P ⊗ (pointIntegralComplexSections D l E).obj J.obj ⟶
      (pointIntegralComplexSections D l E).obj (total D l E C.obj J.obj)) : Prop :=
  PointSectionsCompletionEquation D l E hl S canonical P C J rho eta beta
```

The public import list adds:

```lean
public import Sheaf.Paper.PointSectionsBalancingCompletion
```

## Users

`tools/downstream.py Sheaf.Paper.PointEvaluationCompletionNormalization --uses betaCompletionEquation`
finds no downstream module; only the item itself mentions the declaration.
No module needs adaptation. The same predicate is used in the normalization
statement and in the private sections interface. Every target meaning is
unchanged because the new body is definitionally the same strict equation.
The item node gains the construction-owned predicate's node as a statement
dependency; the new node has no dependency path back to the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PointEvaluationCompletionNormalization | A7 | Identical strict chain equation, shared with its construction module. |

## Status

landed 20261026T022753-L-431069 2026-10-26 (merge of deliver/A7/Sheaf.Paper.PointEvaluationCompletionNormalization)
