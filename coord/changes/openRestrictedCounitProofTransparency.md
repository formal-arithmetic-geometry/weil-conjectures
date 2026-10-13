# AlgebraicGeometry.SingleComplexBaseChange.openRestricted_counit_compatibility_aux

## Reason

Implement the counit factorization while keeping the large selected tensor and derived
functors abstract during elaboration. Preflight conservatively classifies added attribute
and option commands as a potential interface change and therefore requires this record.
Every reducibility attribute is local; the derived-category alias is private and its
instance attribute is local. It reuses the supplied instances and chooses no new data.
No exported statement, definition, instance, notation, or public import changes.

## Old

The exported theorem signature is:

```lean
theorem openRestricted_counit_compatibility_aux
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv
```

The module set `autoImplicit false` and had no local transparency attributes.
Its theorem proof was `by sorry`.

## New

The exported theorem signature is identical:

```lean
theorem openRestricted_counit_compatibility_aux
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (derivedPullback (pullback.snd g' U.ι)).map (openRestrictionRepresentativeIso U.ι P).hom ≫
        openRestrictedCompositionMap g' U (DerivedCategory.Q.obj P) ≫
        (derivedPullback (pullback.fst g' U.ι)).map
          ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      (counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P)) ≫
        (openRestrictedTensorDerivedIso g' U P).inv
```

The proof is complete. The added proof-local abstraction and instance alias are:

```lean
attribute [local irreducible] derivedPullback
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh

private abbrev schemeModulesDerived
    [d : ∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) : HasDerivedCategory.{w} Y.Modules := d Y

attribute [local instance] schemeModulesDerived
```

The final theorem also locally marks the representative and tensor-square constructions
irreducible. File-local elaboration options are set explicitly; the final theorem uses
transparency-respecting elaboration, with the final definitional identification checked
with relaxed transparency. These options do not propagate to importing modules.
The additional nonpublic `import all` provides already proved generic private helpers
from `Sheaf.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare`.

## Users

`tools/downstream.py` with `--direct --uses` identifies the following direct importer
and declaration occurrences. The full import closure has 1363 downstream modules, all
with the same statements and definitions because these commands are local to this file.
No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux | T3 | Proves the unchanged theorem; local proof elaboration only. |
| Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorization | unclaimed | Applies the same theorem at the same type; no edit required. |

## Status

landed 20261013T234523-L-2167870 2026-10-13 (merge of deliver/T3/Sheaf.AlgebraicGeometry.OpenRestrictedCounitFactorizationAux)
