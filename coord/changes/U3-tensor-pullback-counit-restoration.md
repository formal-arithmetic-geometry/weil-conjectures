# AlgebraicGeometry.tensorPullbackComposition_localized_homotopy_counit

## Reason

The assigned module and its node were removed by the previous batch rollback.
The worker brief still assigns this item; the delivery restores its original mathematical
interface with a complete proof. Preflight classifies the restoration as a new module.
No existing definition or statement is changed, and no target needs a changed meaning.
Local transparency settings prevent unnecessary unfolding during elaboration; they are
not exported changes to tensorPullback or derivedPullback.

## Old

The module and declaration are absent from the current base. The historical assigned
statement was recorded in the repair diff of
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization`.
Its f, g, K, selected epsilon/a/b/c/M, and equality to the concrete apex are restored below.
Explicit type annotations on the existing let-bindings elaborate to the same signature.

## New

```lean
theorem tensorPullbackComposition_localized_homotopy_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let epsilon {A B : Scheme.{u}} (s : A ⟶ B) :
        DerivedCategory.Qh ⋙ derivedPullback.{u, w} s ⟶
          (Scheme.Modules.tensorPullback s).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let a {A B : Scheme.{u}} (s : A ⟶ B) :
        Scheme.Modules.tensorPullback s ⊣ Scheme.Modules.pushforward s :=
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
    let b {A B : Scheme.{u}} (s : A ⟶ B) :
        (Scheme.Modules.tensorPullback s).mapHomotopyCategory (.up ℤ) ⊣
          (Scheme.Modules.pushforward s).mapHomotopyCategory (.up ℤ) :=
      (a s).mapHomotopyCategory (ComplexShape.up ℤ)
    let c : Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
        Scheme.Modules.tensorPullback (f ≫ g) :=
      (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
      (Scheme.Modules.pushforwardComp f g).symm
    let M := ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K
    ((derivedPullback f).map ((epsilon g).app M) ≫
      (epsilon f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app M)) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((b (f ≫ g)).counit.app K) = derivedCompositionCounitApex f g K
```

The declaration is proved without adding any sorry or changing a definition.
The file has its original public import of DerivedCompositionCounitApex, with all
three proved helpers private. No adapted modules are delivered.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TensorPullbackCompositionHomotopyCounit | U3 | Restores the assigned statement and proves it. |

No module on the current base imports the restored module or mentions its declaration.
In particular the parent normalization module is not adapted in this delivery.
There is no existing user requiring a forced adaptation.

## Status

landed 20261014T083746-L-4168510 2026-10-14 (merge of deliver/U3/Sheaf.AlgebraicGeometry.TensorPullbackCompositionHomotopyCounit)
