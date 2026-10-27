# lisseHomModuleDerivedCategory

## Reason

The existing instance alias repeats the native category instance on the same derived category.
Make it an abbreviation with the identical inferInstance body. This exposes the shared instance
when checking Hom, IsIso and evaluation-coordinate types. The categories, objects, morphisms,
instance fields and mathematical meaning are unchanged. No target statement changes.

## Old

```lean
@[instance_reducible] def lisseHomModuleDerivedCategory
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Category.{u + 1} (Etale.DerivedCategoryModule R T) := inferInstance
```

## New

```lean
abbrev lisseHomModuleDerivedCategory
    (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    Category.{u + 1} (Etale.DerivedCategoryModule R T) := inferInstance
```

The constant-sheaf alias has the same issue and the same consumers. Its body is unchanged.

### Constant-functor old

```lean
def lisseHomConstantFunctor (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    ModuleCat.{u + 1} R ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)
```

### Constant-functor new

```lean
abbrev lisseHomConstantFunctor (R : Type (u + 1)) [CommRing R] (T : Scheme.{u}) :
    ModuleCat.{u + 1} R ⥤ Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)
```

## Users

The current tools/downstream.py --uses result lists exactly these three modules.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteFreeHomEvaluationCoordinates | unclaimed | identical category instance body |
| Sheaf.Paper.FiniteFreeHomLocalCalculation | unclaimed | no edit; consumer compiled in the set |
| Sheaf.Paper.EtaleLisseHomReduction | E8 | proof checks against shared category instance |

The two new calculation modules use the same native category. No forced adaptation is needed.
The arrow module held by Q5 is unchanged.

## Status

landed 20261026T065553-L-3086827 2026-10-26 (merge of deliver/E8/Sheaf.Paper.EtaleLisseHomReduction)
