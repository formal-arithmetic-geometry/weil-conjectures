# ProEtale bounded-continuity proof scope

## Reason

The completed proof introduces the private instance
`AlgebraicGeometry.Scheme.ProEt.ringEvaluation_additive` so that the existing
evaluation functor can be used by the derived-section comparison. The static
interface checker conservatively classifies this private instance declaration as
an interface change and therefore requires a change record. The instance is
proof support only; no target statement, definition, public import, or existing
signature changes, and no downstream adaptation is required.

## Old

The item module contained the original declarations with the target theorem
proofs left as `sorry`. It had no private evaluation-additivity instance.

## New

The item retains the same public imports, declarations, signatures, and
definitions. It adds the following private proved instance for use only while
elaborating the module's comparison proof:

```lean
private instance ringEvaluation_additive (X : Scheme.{u})
    (R : Sheaf (topology X) RingCat.{u + 1}) (U : X.ProEt) :
    (SheafOfModules.evaluation.{u + 1} R (op U)).Additive := ⟨by intros; rfl⟩
```

No imported module refers to this private name, and no downstream module needs
adaptation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections` | T5 | Private proof instance added. |

The new name is private and has no external users. Existing signatures and public
imports are unchanged, so no consumer requires adaptation.

## Status

landed 20261019T005428-L-2769294 2026-10-19 (merge of deliver/T5/Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections)
