# AlgebraicGeometry.open_derived_localizations_and_adjunction

## Reason

The retire item marks this Sheaf twin DIFFERENT: upstream now splits its three
clauses into separate theorems. The old combined theorem has the same fully qualified
name as the upstream adjunction-only theorem. Importing the upstream module in the
original Sheaf module fails with `AlgebraicGeometry.open_derived_localization_adjunction
has already been declared`. Keep the full combined statement under a distinct name,
and prove it by composing upstream's three proved results. No target or definition
changes. No upstream source file changes.

## Old

```lean
theorem open_derived_localization_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    ∃ hO : ∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W)),
    letI := hO
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
```

## New

```lean
theorem open_derived_localizations_and_adjunction
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U : X.Opens) :
    ∃ hD : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
    letI := hD
    ∃ hO : ∀ W : U.toScheme.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over W)),
    letI := hO
    ∃ (R : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory X),
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
```

The type is identical after renaming the declaration. The old fully qualified name
belongs to the existing upstream adjunction-only theorem, whose signature is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction | M5 | Rename combined theorem and compose proved upstream results. |

`tools/downstream.py Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
--uses AlgebraicGeometry.open_derived_localization_adjunction` reports zero downstream
modules and only the declaration in this module as a textual use. Searches of
`lean/Sheaf` and `quarantine/Sheaf` find no importers or applications. The six consumers
listed in the retire inventory now live in `WeilConjectures` and already import the
upstream module and use its split API; they remain unchanged. DAG parent citations
are preserved by keeping this node and all three clauses, with its Lean attachment
updated to the distinct combined theorem. The unit route is unchanged.

## Status

landed 20261020T221250-L-4166153 2026-10-20 (merge of deliver/M5/Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction)
