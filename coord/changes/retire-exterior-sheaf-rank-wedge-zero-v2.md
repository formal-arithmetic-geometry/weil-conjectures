# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_rank_wedge_eq_zero

## Reason

Retire `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero` under the
2026-10-20 retirement hand-off. Its adopted source-library twin is fully proved,
but uses the official `exteriorPower`/`wedge` construction while the three Sheaf
consumers retain the older `exteriorSheaf`/`exteriorSheafSection` interface.

## Old

```lean
-- Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero
 theorem exteriorSheaf_rank_wedge_eq_zero {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (r n s : ℕ) (hr : n = r + s) [A.IsFiniteLocallyFreeOfRank r]
    (U : X.Opens) (a : Fin r → A.val.obj (op U))
    (c : Fin s → B.val.obj (op U)) (j : Fin s) (d : A.val.obj (op U))
    (hc : c j = f.val.app (op U) d) :
    exteriorSheafSection B n U
      (fun i ↦ Fin.append (fun k ↦ f.val.app (op U) (a k)) c (Fin.cast hr i)) = 0
```

## New

The retired module is removed. The node points to the adopted source theorem
`WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero`, whose
proved declaration has the same hypotheses and vanishing conclusion with
`wedge` in `exteriorPower B n`. The two consumers that need the old section
formula add a private compatibility helper: apply the upstream theorem and
transport through the proved `exteriorSheafPowerIso` inverse wedge formula.
The third consumer drops the unused rank-module import entirely. Its current
upstream chart-comparison import and the presheaf comparison rewrites are retained.
No public theorem signature changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearBijective | unclaimed | Remove the unused retired Sheaf rank import; no replacement rank import is needed. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantSplitLinearMaps | unclaimed | Replace the import and use a private compatibility helper for the rank-vanishing call. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantWedgeQuotientFactor | unclaimed | Replace the import and use a private compatibility helper for the rank-vanishing call. |

## Status

landed 20261020T163703-L-3786630 2026-10-20 (merge of deliver/V2/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero)
