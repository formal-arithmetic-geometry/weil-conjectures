# arithmeticRoosMap

## Reason

The strict finite-stage horizontal theorem needs the canonical arithmetic map below the completion coherence module. Extracting this existing definition prevents an import cycle.

## Old

In `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence`:

```lean
noncomputable def arithmeticRoosMap
    {A : Type x} [Category.{y} A] [Abelian A] [HasCountableProducts A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction A e).obj X) :=
  strictRoosMapOfSquare (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)
```

## New

In `Sheaf.Algebra.Homology.ArithmeticRoosMap`, publicly imported by the original module:

```lean
noncomputable def arithmeticRoosMap
    {A : Type x} [Category.{y} A] [Abelian A] [HasCountableProducts A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    roosF.obj X ⟶ roosF.obj ((complexRestriction A e).obj X) :=
  strictRoosMapOfSquare (selection e X.asFunctor) (block e X.asFunctor)
    (strictRoosBlock_comm X e he)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence | B4 | public import preserves the original API |
| Sheaf.Algebra.Homology.FiniteFreeQuotientRoosHorizontalCoherence | B4 | new strict theorem imports this API |

## Status

landed 20261025T201357-L-2465468 2026-10-25 (merge of deliver/B4/Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence)
