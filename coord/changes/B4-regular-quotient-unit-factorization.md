# regularQuotientCompletionUnit

## Reason

The original inline strict-augmentation compatibility proof repeatedly unfolds the
concrete tensor and quotient tower during elaboration, costing about 16 seconds
per occurrence. Factor this same Roos construction through the abstract tower and
augmentation arguments of `principalTowerRoosUnit`. The original body and the new
one are definitionally equal, including the proof-irrelevant compatibility proof.
All coordinate formulas, the actual map, and all declaration signatures are kept.
This is an elaboration repair, with no change to the mathematical statement or to
target meaning. The new generic construction has real data and no postponed proof.

## Old

```lean
def regularQuotientCompletionUnit
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    P ⟶ regularQuotientCompletion R P a :=
  roosAugment (X := koszulTowerComplex R (reductionTensorTower R P a))
    (fun n ↦ (regularQuotientAugmentation R P a).app (op n))
    (fun n ↦ ((regularQuotientAugmentation R P a).naturality
      (homOfLE (Nat.le_succ n)).op).symm.trans (Category.id_comp _))
```

## New

```lean
def regularQuotientCompletionUnit
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    P ⟶ regularQuotientCompletion R P a := by
  unfold regularQuotientCompletion
  exact principalTowerRoosUnit R P (reductionTensorTower R P a)
    (regularQuotientAugmentation R P a)
```

`principalTowerRoosUnit` is the generic `roosAugment` construction in the new
`Sheaf.Paper.PrincipalKoszulRoosPresentationComparison` module. That module is a
public import because the public definition now refers to this real construction.
The same factorization is used by the newly introduced principal Koszul Roos unit.
Local irreducibility of the concrete tensor towers keeps their implementation out
of type comparisons; these local settings change no exported attribute. Profiling
reduced the helper check from roughly 58 seconds to 17 seconds.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RegularQuotientCompletionUnit | B4 | Definitionally equal factorization; proof completed by this packet. |
| Sheaf.Paper.FiniteFreeQuotientCompletion | unclaimed in current shared claim records | No source adaptation: the unit's type and map are unchanged. |

`tools/downstream.py Sheaf.Paper.RegularQuotientCompletionUnit --uses
regularQuotientCompletionUnit` lists just these two users and the one downstream
module. No adopted source-library declaration or import is changed.

Validation: the unchanged downstream consumer compiles cleanly against the packet
(7.7 seconds). An `rfl` proof against the exact original inline body compiles
(26.7 seconds). The final main module compiles cleanly in 29.9 seconds.

## Status

landed 20261021T182247-L-1170264 2026-10-21 (merge of deliver/B4/Sheaf.Paper.RegularQuotientCompletionUnit)
