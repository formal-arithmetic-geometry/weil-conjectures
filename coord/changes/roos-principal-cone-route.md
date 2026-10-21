# WeilConjectures.roosIntrinsicCompletenessEquivalence

## Reason

Use the actual integral coefficient ring and normalized quotient tower directly.
The earlier general reflector and completed-coefficient interfaces do not directly
instantiate at the independent site and coefficient universes of this statement.
The new cone construction and quotient comparison avoid those detours.

## Old

The item imported these modules publicly:

```lean
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.KoszulReconstruction
```

Its sole theorem proof was `by sorry`. All 20 existing declaration signatures and
all existing definition bodies are preserved verbatim in this delivery.

## New

Remove those two unused public imports. Add private proof imports of the explicit
principal cone construction, singleton local criterion, normalized quotient
augmentation and unit-preserving Roos comparison. Replace the theorem proof with
the assembly from those declarations. The proofs of `integralKoszulStep_square`, `integralKoszulUnit_compatible`
and the private `integralKoszulProductUnit_comp` now apply the generic cone
identities directly. No existing statement or definition changes.
No adopted source-library module is edited.

The regular quotient augmentation is proved from the existing normalized regular
quotient interface and `PrincipalKoszulStrictReplacement.completed_exact`.
The new data definitions are explicit constructions. The single retained proof
obligation is a named singleton completion theorem in its own module with a source,
complete proof plan and DAG node. The module documentation and main DAG proof now
follow the actual route.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | D2 | Proof and imports change; signatures and definition bodies stay unchanged. |
| `Sheaf.SixFunctors.OpenRoosUnitAdjunction` | unclaimed | Uses unchanged integral declarations and explicitly imports the general intrinsic implementation; no adaptation. |

No other module directly imports the item. No consumer adaptation is required by a
changed signature or definition. The two removed imports are retained everywhere
else they are still used; no whole module is withdrawn.

## Status

landed 20261021T225104-L-3766544 2026-10-21 (merge of deliver/D2/Sheaf.Paper.RoosIntrinsicCompletenessEquivalence)
