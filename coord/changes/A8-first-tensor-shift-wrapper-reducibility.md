# tensorShiftFirst

## Reason

Kernel conversion of completed tensor composites can unfold the large descent
before this small first-slot shift wrapper. The analogous second-slot wrapper
was repaired in `completed-tensor-shift-wrapper-reducibility.md`. Make the first
wrapper an abbreviation too. Its type and term are identical; only the
reducibility hint changes. This is needed to compile the assigned first-slot
existence and uniqueness proof within the delivery limit.

## Old

```lean
def tensorShiftFirst (A : Type v) [Category.{w} A] [HasShift A ℤ] (r : ℤ) :
    A × A ⥤ A × A := (shiftFunctor A r).prod (𝟭 A)
```

## New

```lean
abbrev tensorShiftFirst (A : Type v) [Category.{w} A] [HasShift A ℤ] (r : ℤ) :
    A × A ⥤ A × A := (shiftFunctor A r).prod (𝟭 A)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed | Same predicates; wrapper unfolds first. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | A8 | Avoids expanding the completed tensor descent during conversion. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Definitionally identical product functor; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | H7 | Definitionally identical product functor; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorShiftAddOnGood | unclaimed | Identical predicate and product functor; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed | Identical product functor; no adaptation. |
| Sheaf.SixFunctors.IndependentExpressionShiftNaturality | unclaimed | Identical product functor; no adaptation. |
| Sheaf.SixFunctors.SystemTensorLeftShiftUnique | unclaimed | Definitionally identical product functor; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed | Definitionally identical product functor; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed | Definitionally identical product functor; no adaptation. |

The eight current declaration users were rechecked on 2026-10-26 with
`tools/downstream.py Sheaf.SixFunctors.IntegralTensorShiftProperties --uses tensorShiftFirst`.
The two additional users, BasicSystemShiftResolutionCalculus and
SystemTensorShiftCoherence, are preserved at their quarantine paths in
`coord/rework.tsv` (2026-10-25T22:18:42Z); they are not withdrawn by this delivery.
The remaining transitive importers retain identical declaration types and bodies.
The three additional current users listed above were read against the unchanged
wrapper and predicate meanings. They have not been recompiled in this resumed
attempt: the complete-packet compiler stops at a missing shared import artifact.
No consumer signature or proof is changed. The module being repaired is
unclaimed; no file held by another group is adapted.

Targets using this definition have exactly the same meaning: shift the first
factor and leave the second fixed. The factored definition compiled, and a separate mirrored check proved its
exact equality with the old predicate by `Iff.rfl`. The three current direct
consumers compiled unchanged against the patched dependency:
`IntegralOperationShiftData`, `SystemTensorLeftShiftUnique`, and
`SystemTensorShiftRepresentativeModels`. The two quarantined consumers are preserved
without adaptation; this check does not restore them.

Definition review can verify that the term is
verbatim unchanged; no hypothesis, conclusion, object or morphism changes.

This definition change reopens meaning review for affected targets under
AGENTS.md §4; the verbatim types and bodies are the evidence for that review.

## Status

landed 20261026T022806-L-446879 2026-10-26 (merge of deliver/A8/Sheaf.SixFunctors.IntegralTensorLeftShiftUnique)
