# Exact tower augmented counit evaluation: private proof scopes

## Reason

The interface checker conservatively flags the section-variable commands supporting
proved private helpers. The returned delivery is repaired by removing its seven
duplicate factorization lemmas. Their four needed conclusions are reused through proof-only
`import all` of the existing normalization modules. These imports make the existing
private helpers available in this proof without modifying their owner modules. All
original public signatures, composite map definitions and public imports in the
item remain verbatim.

## Old

The existing universe command, retained verbatim in the repaired packet:

```lean
universe uA vA uB vB wA wB wTA wTB uC vC uD vD rA rB
```

There was no `TransitionLaws` section. The existing `Maps` section and its public
variable block and four definitions already existed.

## New

The universe command is unchanged; the returned packet's extra `wC` is removed
along with its duplicate composition-factorization lemma. The new section is
closed before the original public definitions:

```lean
section TransitionLaws

variable (A : Type uA) [Category.{vA} A] [Abelian A]
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wTA} (ℕᵒᵖ ⥤ A)]

-- Fully proved private lemmas transition_id and constant_transition.

end TransitionLaws
```

Declaration-scoped backward-definitional-equality and transparency options support
the remaining private helpers and the main proof. They do not change any type.

The two proof-only imports expose the existing private helpers to this module:

```lean
import all Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
import all Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
```

The original public imports remain verbatim. This is the module system's native
mechanism for proof access to private declarations; it introduces no copied lemma,
new public declaration, or change in a normalization module.

## Users

The item theorem retains precisely its original signature. Its sole consumer uses
the same theorem without adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation | A9 | One proof completed. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | unclaimed | Interface unchanged. |

## Status

landed 20261024T014412-L-2191533 2026-10-24 (merge of deliver/A9/Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation)
