# SheafOfModules.RingedPushforwardPureTensor

## Reason

Use the existing canonical pure-tensor function to avoid repeating its large
sheafification expression in the public normalization predicate. The old and new
bodies are definitionally equal: an independent scratch check of their equivalence
compiled with `Iff.rfl`. This changes neither the mathematical statement nor any
binder, universe, or theorem signature. The target statements remain unchanged.

## Old

```lean
def RingedPushforwardPureTensor
    (L : (pushforward.{w} c).LaxMonoidal) : Prop :=
  ∀ (M N : CategoryTheory.ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (pushforward.{w} c) L M N).val.app U
      ((tensorObjIsoSheafification ((pushforward c).obj M) ((pushforward c).obj N)).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R).obj)).unit.app
            (((pushforward c).obj M).val ⊗ ((pushforward c).obj N).val)).app U
              (x ⊗ₜ[R.obj.obj U] y))) =
      (tensorObjIsoSheafification M N).inv.val.app (v.op.obj U)
        (((PresheafOfModules.sheafificationAdjunction
          (𝟙 ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S).obj)).unit.app
            (M.val ⊗ N.val)).app (v.op.obj U) (x ⊗ₜ[S.obj.obj (v.op.obj U)] y))
```

## New

```lean
def RingedPushforwardPureTensor
    (L : (pushforward.{w} c).LaxMonoidal) : Prop :=
  ∀ (M N : CategoryTheory.ringedSiteModules.{w}
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (U : Cᵒᵖ) (x : M.val.obj (v.op.obj U)) (y : N.val.obj (v.op.obj U)),
    (@Functor.LaxMonoidal.μ _ _ _ _ _ _ (pushforward.{w} c) L M N).val.app U
      (CategoryTheory.CochainPullback.moduleTmul (R := R)
        ((pushforward c).obj M) ((pushforward c).obj N) U x y) =
      CategoryTheory.CochainPullback.moduleTmul (R := S) M N (v.op.obj U) x y
```

## Users

`tools/downstream.py` reports zero downstream modules; its declaration-use search
reports only the assigned module. A source search of both library roots agrees.
No consumer adaptation is needed. The canonical function's module is added as a
public import because the public definition now refers to it.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax | G5 | Definitionally equal normalization; theorem proved. |

## Status

landed 20261024T185827-L-3703466 2026-10-24 (merge of deliver/G5/Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax)
