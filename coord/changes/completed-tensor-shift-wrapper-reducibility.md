# completedTensorShiftSecond

## Reason

The second-input shift is a wrapper around the product of the identity and shift
functors. Kernel conversion of large composites can unfold the completed tensor
descent before this wrapper. Making the wrapper an abbreviation makes its actual
product functor available first. The signature and body are unchanged, so every
existing statement has the same definitional meaning. No consumer adaptation is needed.

## Old

```lean
noncomputable def completedTensorShiftSecond (A : Type a) [Category.{b} A] [HasShift A ℤ]
    (r : ℤ) : A × A ⥤ A × A :=
  (𝟭 A).prod (shiftFunctor A r)
```

## New

```lean
noncomputable abbrev completedTensorShiftSecond (A : Type a) [Category.{b} A] [HasShift A ℤ]
    (r : ℤ) : A × A ⥤ A × A :=
  (𝟭 A).prod (shiftFunctor A r)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CompletedTensorShiftRight | J8 | Proof conversion unfolds the small shift wrapper first. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Existing signatures and definitions remain definitionally equal. |

The target signatures are unchanged. Any definition review sees the identical
product of the identity functor and the shift functor; no mathematical data changes.

## Status

landed 20261020T230756-L-611403 2026-10-20 (merge of deliver/J8/Sheaf.SixFunctors.CompletedTensorShiftRight)
