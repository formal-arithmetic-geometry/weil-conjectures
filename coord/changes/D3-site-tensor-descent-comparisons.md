# CategoryTheory.tensorDescentComplexIso

## Reason

The comparison definitions formerly repeat long projections of the nested descent
witness. Use the named, proved existence APIs in the descent module. Both selected
functors and comparisons remain definitionally equal to the original choices by
proof irrelevance. The same change applies to tensorDescentDerivedIso. No hypothesis,
mathematical data or normalization changes.

## Old

```lean
def tensorDescentComplexIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
      J R).choose_spec.2.2.1
    |>.choose_spec.1.some

def tensorDescentDerivedIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
      J R).choose_spec.2.2.1
    |>.choose_spec.2.choose_spec.some
```

## New

```lean
def tensorDescentComplexIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteHomotopyTensorExistsIndependentCoefficients.{u, v, r, w}
    J R).choose_spec.1.some

def tensorDescentDerivedIso [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :=
  (SheafOfModules.siteDerivedTensorExistsIndependentCoefficients.{u, v, r, w} J R).choose_spec.some

```

## Users

The source scan finds no current Lean importer and only this module mentions either
comparison. The unfinished DAG parents and the unit route remain attached and unchanged;
this delivery preserves the module and proves its assigned statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SiteDerivedTensorRestriction | D3 | Definitionally equal selections; proof uses the compact APIs. |

## Status

landed 20261021T233637-L-842487 2026-10-21 (merge of deliver/D3/Sheaf.Paper.SiteDerivedTensorRestriction)
