# WeilConjectures.automorphismConstructibleStage_integral_shift_data

## Reason

Replace the theorem's single proof hole by the generator calculation, coherent signed
Roos shift and normalized derived descent. Added helpers are private and proved. Added
imports are proof imports. The additional namespace, local elaboration settings and
local proof attributes are recorded for the interface checker; no public statement,
public definition, exported instance or public import is changed.

## Old

```lean
theorem automorphismConstructibleStage_integral_shift_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d
```

Its proof was `by sorry` and there were no private shift-construction helpers in this module.

## New

```lean
theorem automorphismConstructibleStage_integral_shift_data
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∀ (Z W : Scheme.{u}) (g : Z ⟶ W),
      ∃ (c : (integralOperationsPullbackComplexFunctor l E g).CommShift ℤ)
        (d : (integralDerivedPullback l E g).CommShift ℤ),
        IntegralCompletedComparison.ShiftCoordinates l E g c ∧
          IntegralCompletedComparison.ShiftDescent l E g c d
```

The statement is verbatim unchanged. The proof now constructs both shift structures,
verifies the two prescribed mapping-cocone coordinates, and proves the precise comparison
normalization on every good representative. The new private definitions are actual
constructions from the existing additive level, product, cone and descent APIs. None
chooses data from a mere unproved existence statement. No target's meaning is changed.

## Users

`tools/downstream.py --uses automorphismConstructibleStage_integral_shift_data` finds
only the item and the direct consumer below as textual users among the 1840 downstream
modules. All downstream interfaces are preserved; no consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AutomorphismConstructibleIntegralShiftData | D7 | Private proof helpers; same public theorem |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | T3 | Same theorem name, binders and conclusion; no adaptation |

## Status

landed 20261028T034727-L-3538125 2026-10-28 (merge of deliver/D7/Sheaf.Paper.AutomorphismConstructibleIntegralShiftData)
