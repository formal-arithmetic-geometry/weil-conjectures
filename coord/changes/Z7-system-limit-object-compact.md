# SheafOfModules.system_limit_object

## Reason

Move the already proved identity and composition laws into named private theorems. The levels and transitions are unchanged. The record now refers to compact theorem applications when another construction reduces its projections.

This is part of proving the abelian structure in the item module. The complete file
repeatedly exceeded the fixed compile limit. All changed definitions are private
proof constructions; no public statement, public definition body or target meaning
is changed. The public abelian instance remains the choice from its unique-existence
theorem, whose proof is filled in this delivery.

## Old

```lean
private def system_limit_object {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : StrictRingSystem B where
  level n := limit (F ⋙ systemEvaluation B n)
  transition h := system_limit_transition F h
  identity n U x := by
    let R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op n))
    have he : (toSheaf R).map (system_limit_transition F (Nat.le_refl n)) =
        𝟙 ((toSheaf R).obj (limit (F ⋙ systemEvaluation B n))) := by
      apply (isLimitOfPreserves (toSheaf R)
        (limit.isLimit (F ⋙ systemEvaluation B n))).hom_ext
      intro j
      change _ ≫ (toSheaf R).map (limit.π (F ⋙ systemEvaluation B n) j) =
        _ ≫ (toSheaf R).map (limit.π (F ⋙ systemEvaluation B n) j)
      rw [system_limit_transition_forget]
      ext V y
      change ((F.obj j).transition (Nat.le_refl n)).val.app V
          ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y) =
        (limit.π (F ⋙ systemEvaluation B n) j).val.app V y
      rw [(F.obj j).identity]
    exact congrArg (fun f : (toSheaf R).obj (limit (F ⋙ systemEvaluation B n)) ⟶
      (toSheaf R).obj (limit (F ⋙ systemEvaluation B n)) ↦ f.hom.app U x) he
  compose {l m n} h k U x := by
    let R (i : ℕ) :=
      (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj (B.obj (op i))
    have he : (toSheaf (R n)).map (system_limit_transition F (h.trans k)) =
        (toSheaf (R n)).map (system_limit_transition F k) ≫
          (toSheaf (R m)).map (system_limit_transition F h) := by
      apply (isLimitOfPreserves (toSheaf (R l))
        (limit.isLimit (F ⋙ systemEvaluation B l))).hom_ext
      intro j
      change _ ≫ (toSheaf (R l)).map (limit.π (F ⋙ systemEvaluation B l) j) =
        _ ≫ (toSheaf (R l)).map (limit.π (F ⋙ systemEvaluation B l) j)
      rw [system_limit_transition_forget, Category.assoc, system_limit_transition_forget,
        ← Category.assoc, system_limit_transition_forget]
      ext V y
      change ((F.obj j).transition (h.trans k)).val.app V
          ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y) =
        ((F.obj j).transition h).val.app V
          (((F.obj j).transition k).val.app V
            ((limit.π (F ⋙ systemEvaluation B n) j).val.app V y))
      rw [(F.obj j).compose]
    exact congrArg (fun f : (toSheaf (R n)).obj (limit (F ⋙ systemEvaluation B n)) ⟶
      (toSheaf (R l)).obj (limit (F ⋙ systemEvaluation B l)) ↦ f.hom.app U x) he
```

## New

```lean
private def system_limit_object {K : Type} [SmallCategory K] [FinCategory K]
    (F : K ⥤ StrictRingSystem B) : StrictRingSystem B where
  level n := limit (F ⋙ systemEvaluation B n)
  transition h := system_limit_transition F h
  identity n U x := system_limit_identity F n U x
  compose h k U x := system_limit_compose F h k U x
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.SystemLevelLeftExtension --uses
system_isLimit system_isColimit` lists only the item module. The object constructors
are private to that same module. No downstream module can use their private names.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.SystemLevelLeftExtension | Z7 | Internal proof witnesses use the compact construction; public interfaces stay identical. |

## Status

landed 20261020T221409-L-4183604 2026-10-20 (merge of deliver/Z7/Sheaf.CategoryTheory.SystemLevelLeftExtension)
