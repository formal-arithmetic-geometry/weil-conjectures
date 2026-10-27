# AlgebraicGeometry.ProEtale.AmbientClopenRestriction.sections

## Reason

The system branch returns only the underlying abelian presheaf. Evaluating the module
first unnecessarily transports its scalar structure through the coefficient-ring equality,
which makes subsequent conversion of section and transition formulas expensive. Forget the
module structure first and then evaluate the presheaf along the fixed-level inclusion.
Evaluation changes only scalar structure; its carrier, addition, restrictions and maps are
exactly these underlying presheaf data. Thus the resulting abelian presheaf functor is the
same. No target signature or coefficient category changes. Targets using this definition
should be reread with this definitional refactoring.

Mathlib `PresheafOfModules.pushforwardCompToPresheaf` records exactly this compatibility
and is constructed as `Iso.refl _`. Evaluation is the module pushforward along `Prod.sectR`
with the published coefficient-ring equality.

## Old

```lean
def sections (m : Option ℕ) (X : Scheme.{u}) (n : ℕ) :
    Modules l E m X ⥤ X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  match m with
  | some _ => SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _
  | none => VaryingRing.eval (scalarRings l E) (scalarTransitions l E) X n ⋙
      SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _
```

## New

```lean
def sections (m : Option ℕ) (X : Scheme.{u}) (n : ℕ) :
    Modules l E m X ⥤ X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  match m with
  | some _ => SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _
  | none => SheafOfModules.toSheaf _ ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj (Prod.sectR n X.ProEt).op
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | R2 | same underlying section presheaf |

`tools/downstream.py ... --uses sections` reports only this item and zero downstream
modules in the current source. No forced adaptations.

## Status

landed 20261025T181016-L-4062981 2026-10-25 (merge of deliver/R2/Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness)
