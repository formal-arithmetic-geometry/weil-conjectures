# AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_backward

## Reason

Retire the duplicate Sheaf module under the human-approved retirement hand-off in
coord/changes/retire-sheaf-twins-20261020.md and its row in coord/retire-items.tsv.
The prerequisites FiniteLocalAbelianForget, TorsionEtaleSheaf, and
TorsionSheafCharacterizations already use their adopted upstream modules.
The replacement theorem has the exact same signature and a complete proof.
The upstream private finiteLocalSets_of_iso now explicitly uses
isFiniteSheaf_of_finite_algClosed_stalks, an interface change internal to its proof.
It does not change the public theorem.

## Old

From Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward:

```lean
theorem isConstructibleSheaf_integral_backward {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : X.IsTorsionAbelianSheaf F) : let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙ ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom IsConstructibleEtaleSheafOfSets ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) → IsConstructibleSheaf ((sheafCompose X.smallEtaleTopology E).obj F)
```

## New

Use the existing theorem with the verbatim signature above from
WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward.
Withdraw the duplicate with deleted.txt and move only its node's Lean attachment.
Preserve the node's statement, proof, proof dependencies, unit, and audit data.
No definition or target statement changes, so no target review is reopened.
The exact old signature is tested by a separate compilation probe applying the
upstream theorem; this compiled successfully. Both the upstream theorem and the
probe use only propext, Classical.choice, and Quot.sound.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward | S2 (this item) | Withdraw the duplicate module. |
| WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients | unmodified source library | Already imports the upstream twin and applies its theorem at line 95. No edit. |

The current downstream.py scan reports zero downstream modules of the duplicate.
A full Lean import/name scan confirms the only external call is the upstream parent.
The retirement register's former consumer
Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficients is already absent; its DAG
node q1-constructible-integral-coefficients points at the upstream parent. No source
restoration or consumer edit is needed. No quarantined Lean module imports the copy.
The only node with this Lean module attachment is
q1-constructible-integral-coefficients-backward, whose attachment is moved in this
packet. Its dependency edges and the unit route remain available through that node;
this is replacement by an identical public theorem, not pruning its mathematical content.

## Status

landed 20261021T011035-L-2031495 2026-10-21 (merge of deliver/S2/Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward)
