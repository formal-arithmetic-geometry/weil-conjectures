# derivedPullbackComposition_counit_normalization

## Reason

The original statement elaboration timed out at 60 seconds because dependent type
comparison unfolded derivedPullback and related chosen functor/adjunction data.
Use existing definition interfaces locally. The preflight conservatively treats
an added attribute command as an interface change, even though every added
attribute is local. This record documents that classification. No definition
body or public signature is changed.

## Old

No local irreducibility commands. Both backward.isDefEq.respectTransparency and
backward.isDefEq.respectTransparency.types were false. The theorem signature was:

```lean
theorem derivedPullbackComposition_counit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (canonicalDerivedPullbackComposition f g).hom.app
        (((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
      (derivedPullback (f ≫ g)).map
        ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (schemeHomPullbackAdjunction (f ≫ g)).counit.app (DerivedCategory.Qh.obj K) =
      derivedCompositionCounitApex f g K

```

## New

Both modules enable respectTransparency and respectTransparency.types. Definition bodies remain identical;
only their transparency during elaboration in this module is changed:

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh canonicalDerivedPullbackComposition schemeHomPullbackAdjunction
```

The theorem signature is exactly the Old signature. Its proof evaluates the
pinned Hom normalization, opening schemeHomPullbackAdjunction explicitly with delta
only at the characterising Hom formula. It precomposes this equality using congrArg
and transitivity with the strictly smaller localized-counit calculation.
All public imports are retained; both added imports are proof-only. The repair
reuses the existing private counit_of_normalization with import all from
DerivedDirectImagePastedCounitNormalization and deletes the duplicate local helper. The new module uses
local irreducibility for derivedPullback, tensorPullback, Qh and the selected
composition, likewise without exporting those attributes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | T1 | Same statement; concrete proof and local transparency repair. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit | unclaimed | No interface change and no adaptation; original compiles against the delivered overlay. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit | new in T1 delivery | Uses the existing definitions through their interfaces; one documented smaller hole. |

The direct theorem user is DerivedPullbackCompositionMateUnit; all transitive
importers see the identical theorem signature and original public imports. No target
statement or definition used by a target changes its meaning, so statement review
is not reopened. No forced adaptation is delivered.

## Status

landed 20261014T085853-L-234204 2026-10-14 (merge of deliver/T1/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization)
