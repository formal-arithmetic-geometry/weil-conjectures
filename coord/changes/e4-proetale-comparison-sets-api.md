# Set-valued comparison API in ProEtaleComparisonSections

## Reason

The item needs the unit and counit criterion for sheaves of sets. The original module
already proves the affine set-valued sheafification and unit facts in private helpers.
These helpers cannot be referenced from a new importing module. The module is unclaimed
(checked 2026-10-16), so the forced-adaptations instruction permits this addition as work
on an unclaimed module. Append three proved public consequences in that same module,
retaining all original declarations, signatures, visibility, and proofs. The stronger
continuity theorem permits ind-etale stages and removes the separate ring tensor-product
stability obligation from the overlap argument. A private proof import supplies the
proved density criterion. No target definition or statement changes.

## Old

The three declarations below did not exist. Every original declaration and its signature
is retained verbatim. The original file ends with `end AlgebraicGeometry`.

## New

```lean
theorem proEtaleComparisonUnitSets_isIso (X : Scheme.{u}) :
    IsIso (proEtaleSiteComparison X).unit
```

```lean
theorem proEtaleComparisonSets_continuous (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt X).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj G).obj)
```

```lean
theorem proEtaleComparisonCounitSets_isIso_of_continuous (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj)) :
    IsIso ((proEtaleSiteComparison X).counit.app F)
```

## Users

`tools/downstream.py` lists these twelve downstream modules. Its `--uses` checks for
all three new declaration names return zero existing users. The assigned item and
its new continuity module use the new API in this delivery. No pre-existing downstream
module outside the assigned item needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | No edit or interface change. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | {'who': 'E3', 't': 1792123365.8311865, 'since': '2026-10-16T04:02:45Z'} | No edit or interface change. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | {'who': 'E4', 't': 1792123368.8662663, 'since': '2026-10-16T04:02:48Z'} | Uses the new unit and counit criterion; unchanged original signature. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No edit or interface change. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No edit or interface change. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | {'who': 'C4', 't': 1792118210.053856, 'since': '2026-10-16T02:36:50Z'} | No edit or interface change. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No edit or interface change. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | No edit or interface change. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No edit or interface change. |
| TargetsCheck | unclaimed | No edit or interface change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No edit or interface change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No edit or interface change. |

## Status

landed 20261016T054834-L-156595 2026-10-16 (merge of deliver/E4/Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover)
