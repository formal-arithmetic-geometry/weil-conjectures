# fullAffineEtale_cohomology_comparison_point

## Reason

The previous theorem required every natural all-degree comparison to be normalized in degree zero. Negating a comparison violates that assertion on section 1 of the constant integer sheaf over a nonempty affine scheme. Stacks 03YU supplies a natural comparison, not normalization of every possible comparison. The replacement constructs a normalized comparison in degree zero and proves its section formula. The parent theorem keeps its original statement.

## Old

```lean
theorem fullAffineEtale_cohomology_comparison_point (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) (e : ∀ p : ℕ,
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) p ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology p ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj))
      (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (x : Sheaf.H'.{w}
        (((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology).obj G) 0 U) :
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ _
        (Ext.homEquiv₀ (((e 0).app G).hom x))).app (op U.obj))
          (FreeAbelianGroup.of (𝟙 U.obj)) =
      (((sheafificationAdjunction (fullAffineEtaleTopology S) AddCommGrpCat.{u}).homEquiv
        _ _ (Ext.homEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U))
```

## New

```lean
theorem fullAffineEtale_cohomology_comparison_point (S : Scheme.{u})
    [HasExt.{w} (Sheaf (fullAffineEtaleTopology S) AddCommGrpCat.{u})]
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    (U : S.FullAffineEtale) :
    ∃ e :
      (fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology ⋙
        Sheaf.cohomologyPresheafFunctor.{w} (fullAffineEtaleTopology S) 0 ⋙
          (CategoryTheory.evaluation _ _).obj (op U) ≅
      Sheaf.cohomologyPresheafFunctor.{w} S.smallEtaleTopology 0 ⋙
        (CategoryTheory.evaluation _ _).obj (op U.obj),
    ∀ (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
      (x : Sheaf.H'.{w}
        (((fullAffineEtaleInclusion S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (fullAffineEtaleTopology S) S.smallEtaleTopology).obj G) 0 U),
      (((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u}).homEquiv _ _
        (Ext.homEquiv₀ ((e.app G).hom x))).app (op U.obj))
          (FreeAbelianGroup.of (𝟙 U.obj)) =
      (((sheafificationAdjunction (fullAffineEtaleTopology S) AddCommGrpCat.{u}).homEquiv
        _ _ (Ext.homEquiv₀ x)).app (op U)) (FreeAbelianGroup.of (𝟙 U))
```

## Users

Read-only `tools/downstream.py Sheaf.AlgebraicGeometry.FullAffineEtaleTopos --uses fullAffineEtale_cohomology_comparison_point` lists 327 downstream modules and one module mentioning this declaration: the item itself. A search of all Lean sources confirms no external caller.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FullAffineEtaleTopos | K1 | Its comparison proof now obtains the normalized degree-zero witness from this theorem; every other public signature, including the parent theorem, is unchanged. |

All 327 downstream modules use the unchanged exported interfaces or import the module transitively; none uses the corrected declaration. There is no definition change and no target statement change, so the meanings of their statements do not change. No forced adaptation is needed.

## Status

landed 20261012T160828-L-2611503 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.FullAffineEtaleTopos)
