# WeilConjectures.IntegralSystemRealization.completedTensorSlotShiftLaws

## Reason

The proof must identify two presentations of the same completed-coefficient derived category
without unfolding the full standard localization and chosen completed tensor. Local
irreducibility of `HasDerivedCategory.standard`, `integralCompletedTensor`, and `tensorShifts`,
a local priority for the existing `integralTowerHasDerivedCategory` instance, and the existing
backward-definitional-equality interface keep the proof elaboration small. These are local
proof context controls. No definition, instance body, public import, theorem type, or exported
elaboration attribute is changed. The preflight's command-level interface advisory motivates
this explicit record. The new theorem is a generic normalized representative addition lemma.

## Old

```lean
theorem completedTensorSlotShiftLaws (W : Scheme.{u}) :
    ∃ (s₁ : ∀ N : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).flip.obj N).CommShift ℤ)
          (s₂ : ∀ M : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).obj M).CommShift ℤ),
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₁ N) r).app M =
              ((tensorShifts l E).integralLeft W r).app (M, N)) ∧
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₂ M) r).app N =
              ((tensorShifts l E).integralRight W r).app (M, N))
```

## New

The theorem signature is identical:

```lean
theorem completedTensorSlotShiftLaws (W : Scheme.{u}) :
    ∃ (s₁ : ∀ N : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).flip.obj N).CommShift ℤ)
          (s₂ : ∀ M : Integral l E W,
            ((Functor.curry.obj (integralCompletedTensor l E W)).obj M).CommShift ℤ),
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₁ N) r).app M =
              ((tensorShifts l E).integralLeft W r).app (M, N)) ∧
          (∀ (M N : Integral l E W) (r : ℤ),
            (Functor.commShiftIso _ (self := s₂ M) r).app N =
              ((tensorShifts l E).integralRight W r).app (M, N))
```

The added local proof context is:

```lean
attribute [local irreducible] HasDerivedCategory.standard
  integralCompletedTensor tensorShifts
attribute [local instance 3000] integralTowerHasDerivedCategory
set_option backward.defeqAttrib.useBackward true
```

No temporary profiler settings remain. There is no global instance erasure.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | F4 | Proof and local elaboration context only; identical public type. |

`tools/downstream.py` reports zero current downstream modules; the only text occurrence of
the full theorem name is the item itself. Future DAG parents receive the identical theorem
type and component identities. No consumer file is edited.

## Status

landed 20261026T001458-L-2957 2026-10-26 (merge of deliver/F4/Sheaf.SixFunctors.CompletedTensorSlotShiftLaws)
