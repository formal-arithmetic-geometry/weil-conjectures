# WeilConjectures.PurityFiniteSetting.chartCoordinateDifferences_neighbourhood

## Reason

After scoped reducibility improvements and proof-context factoring, the delivery
compiler repeated the accepted large item in 61 seconds, above its 60-second limit.
Relocate its fully proved geometry component to its own module and publicly re-export
it from the item. The user brief, step 3a, permits extraction after definition improvements.
No target statement or data construction changes.

## Old

Location: `Sheaf.Paper.DiagonalDncChartNormalization`.

```lean
def chartCoordinateDifferences {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) :
    pullback h h ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  AffineSpace.homOfVector (pullback.fst h h) fun i ↦
    (pullback.snd h h ≫ u).appTop (AffineSpace.coord V i) -
      (pullback.fst h h ≫ u).appTop (AffineSpace.coord V i)

theorem chartCoordinateDifferences_neighbourhood {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] [IsSeparated u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ (O : (pullback h h).Opens) (s : U ⟶ O.toScheme),
      s ≫ O.ι = pullback.diagonal h ∧
      Etale (O.ι ≫ chartCoordinateDifferences d h u) ∧
      IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) U)
```

## New

Location: `Sheaf.Paper.ChartCoordinateDifferenceNeighbourhood`, publicly imported by
`Sheaf.Paper.DiagonalDncChartNormalization`. Same names, expose attributes, coordinate-map
body and theorem signature:

```lean
def chartCoordinateDifferences {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) :
    pullback h h ⟶ AffineSpace (ULift.{u} (Fin d)) U :=
  AffineSpace.homOfVector (pullback.fst h h) fun i ↦
    (pullback.snd h h ≫ u).appTop (AffineSpace.coord V i) -
      (pullback.fst h h ≫ u).appTop (AffineSpace.coord V i)

theorem chartCoordinateDifferences_neighbourhood {U V : Scheme.{u}}
    (d : ℕ) (h : U ⟶ V) (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    [Etale u] [IsSeparated u]
    (w : u ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V) = h) :
    ∃ (O : (pullback h h).Opens) (s : U ⟶ O.toScheme),
      s ≫ O.ι = pullback.diagonal h ∧
      Etale (O.ι ≫ chartCoordinateDifferences d h u) ∧
      IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) U)
```

The theorem proof is retained. Its etaleness calculation is a proved private helper,
so subsequent cone equations do not retain the large raw-map and translation context.
Only blueprint docstring IDs change to attach this component to its own node.
No existing definition unfolds differently and no consumer requires adaptation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed | Same public names, types and data through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed | Same public names, types and data through re-export; no adaptation. |

## Status

landed 20261026T222700-L-681626 2026-10-26 (merge of deliver/G5/Sheaf.Paper.DiagonalDncChartNormalization)

All three final files passed `lcompile.py --all` under the per-file limit.
The public re-export is checked by the item, which itself uses the relocated names.
