# AlgebraicGeometry.exists_openExtension_derivedAdjunction

## Reason

The assigned item is listed as `retire` in `coord/retire-items.tsv`. Its Sheaf copy
is already proved, with zero holes, and the upstream twin supplies the same mathematical
statement and proof. All prerequisites in the retirement row have been retired.
A fresh scan of both Lean roots finds no current consumer of the Sheaf module.
The historical consumer `Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula`
is already absent; its upstream twin imports the upstream adjunction module.
Withdraw the duplicate and redirect node `lem-pc-open-extension-derived-adjunction`
to the existing upstream declaration.

## Old

The withdrawn declaration in `Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction`:

```lean
theorem exists_openExtension_derivedAdjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∃ J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X,
      ∃ adj : J ⊣ R, True
```

The module publicly imported
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure` and privately imported
`WeilConjectures.Algebra.Homology.DerivedOpenShriekAdjunction`.

## New

The Sheaf module is withdrawn through `deleted.txt`; the delivery tool represents
this withdrawal by an empty module. Its DAG attachment points to the existing declaration
in `WeilConjectures.AlgebraicGeometry.OpenExtensionDerivedAdjunction`:

```lean
theorem exists_openExtension_derivedAdjunction (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    ∃ J : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X,
      Nonempty (J ⊣ R)
```

`Nonempty (J ⊣ R)` and `∃ adj : J ⊣ R, True` are equivalent, without choice or
additional hypotheses. Both implications, and the exact old specialized statement
from the upstream theorem, compile in `scratchpad/Validate.lean`. The upstream
statement, proof, imports, attributes and all other source-library text are unchanged.
No target definition or statement changes. The same unit route is preserved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction | A8 | Withdrawn; zero current importers or declaration users. |

`tools/downstream.py` found zero downstream modules and only the declaration itself
as a textual use of its name. A fresh scan of both Lean roots confirms no importers
of the withdrawn module. The retirement row's historical consumer
`Sheaf.AlgebraicGeometry.OpenExtensionProjectionFormula` has already been retired.
`WeilConjectures.AlgebraicGeometry.OpenExtensionProjectionFormula` already imports
and consumes the upstream twin, with the `Nonempty` pattern, and needs no adaptation.
The sole node attachment is redirected; no other node or consumer changes.

## Status

landed 20261020T141301-L-2031497 2026-10-20 (merge of deliver/A8/Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction)
