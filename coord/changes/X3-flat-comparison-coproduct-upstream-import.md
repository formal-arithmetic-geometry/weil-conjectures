# AlgebraicGeometry.flat_comparison_preserves_countable_coproducts

## Reason

Restore the module quarantined by the 5f7b33eac upstream sync. Its rework row
records a duplicate declaration error: the old public Sheaf derived-pullback
import and its upstream counterpart both provided AlgebraicGeometry.derivedPullback.
The Sheaf module has since been withdrawn and supplies no declarations. The
archived item therefore needs the canonical upstream statement dependency.
This is an import repair of an existing proved module, with zero local holes.

## Old

The archived module's statement import was:

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The archived theorem signature is preserved verbatim:

```lean
theorem flat_comparison_preserves_countable_coproducts
    {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [(Scheme.Modules.tensorPullback f).Additive] :
    PreservesColimitsOfShape (Discrete ℕ) (DerivedCategory.Qh ⋙ derivedPullback f) ∧
      PreservesColimitsOfShape (Discrete ℕ)
        ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Z))
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

Restore the full archived module, changing only this import. The three private
helpers and public proof remain verbatim. All derived-pullback occurrences now
refer to the single upstream definition, consistently with the existing private
DerivedAdjoint import. There is no new definition or statement change and no
upstream file is edited. The existing DAG attachment and dependencies stay valid.

## Users

The source-only downstream.py query with --allow-missing reports no live
importers, because this module and its consumer are quarantined. A separate
search of lean/, quarantine/, and dag/nodes/ finds the direct consumer below.
Its proof applies the unchanged public theorem to f. Its independent quarantine
repair is outside this packet; restoring the dependency supplies its original API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso | unclaimed | Quarantined consumer; original theorem application is preserved. No adaptation. |

The further quarantined normalization consumers retain their DAG dependencies.
No module or declaration is withdrawn, and no unit route or target is changed.

## Status

landed 20261020T174924-L-821871 2026-10-20 (merge of deliver/X3/Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts)
