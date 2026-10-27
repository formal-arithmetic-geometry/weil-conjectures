# chartOrdinaryBaseChange

## Reason

Select the component-isomorphism instance explicitly using `NatIso.isIso_app_of_isIso`.
This replaces a broad instance search; only a proposition-valued proof changes, so
proof irrelevance preserves the entire definition. No statement or data changes.

## Old

```lean
def chartOrdinaryBaseChange (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b) :
    letI := Dnc.compactifiable P f aY
    (Etale.ordinaryFinitePullback P.Coefficient a).obj
      (P.diagonalOrdinaryDualizing f) ≅ P.diagonalOrdinaryDualizing f' :=
  letI := Dnc.compactifiable P f aY
  letI := Dnc.invertibleExponent P (f ≫ aY)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (inferInstanceAs (IsIso
      ((Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq).app (𝟙_ _))))
  (Etale.ordinaryFinitePullback P.Coefficient a).mapIso (P.chartDualizingUnit f).symm ≪≫
    asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) ≪≫
      P.chartDualizingUnit f'
```

## New

```lean
def chartOrdinaryBaseChange (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b) :
    letI := Dnc.compactifiable P f aY
    (Etale.ordinaryFinitePullback P.Coefficient a).obj
      (P.diagonalOrdinaryDualizing f) ≅ P.diagonalOrdinaryDualizing f' :=
  letI := Dnc.compactifiable P f aY
  letI := Dnc.invertibleExponent P (f ≫ aY)
  letI := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension_general
    P.Coefficient f d sq
  letI := (Etale.isIso_dualizingComplexBaseChangeMap_iff P.Coefficient sq).2
    (NatIso.isIso_app_of_isIso
      (Etale.rightDerivedUpperShriekBaseChangeMap P.Coefficient sq) (𝟙_ _))
  (Etale.ordinaryFinitePullback P.Coefficient a).mapIso (P.chartDualizingUnit f).symm ≪≫
    asIso (Etale.dualizingComplexBaseChangeMap P.Coefficient sq) ≪≫
      P.chartDualizingUnit f'
```

## Users

The uses reported by `tools/downstream.py --uses chartOrdinaryBaseChange` were read.
Every use receives the same definitionally equal isomorphism, so no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | explicit instance proof |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | definitionally identical map |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed | definitionally identical map |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | definitionally identical map |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | definitionally identical map |

## Status

landed 20261026T002820-L-117385 2026-10-26 (merge of deliver/T5/Sheaf.Paper.DiagonalDncChartNormalization)
