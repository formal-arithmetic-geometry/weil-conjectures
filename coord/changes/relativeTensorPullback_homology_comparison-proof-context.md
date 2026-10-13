# AlgebraicGeometry.Scheme.relativeTensorPullback_homology_comparison

## Reason

The proof needs private tensor-cone helpers, local notation for the ringed sheaf category,
and more instance synthesis space. The interface detector flags the newly added `open`,
`variable`, and option commands as a context change. All existing declaration signatures,
visibility and public imports remain identical. No public instance or notation is added.
`open CategoryTheory.Limits CochainComplex` is file-local name resolution;
the two transparency options and `synthInstance.maxSize` affect this file's elaboration;
the `variable` command supplies the site and ring parameters of private proved helpers.
The heartbeat option is scoped to the original theorem. None of these commands alters
an imported declaration or the meaning of a target.

## Old

```lean
theorem relativeTensorPullback_homology_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing f.base S.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlat (R := TopCat.Sheaf.inverseImageRing f.base S.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
    (hq : QuasiIso q)
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor P
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (TopCat.Sheaf.inverseImageModule f.base S.sheaf F))
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i))
```

## New

The signature is identical; its complete proof replaces `by sorry`.

```lean
theorem relativeTensorPullback_homology_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eK : DerivedCategory.Q.obj K ≅ E)
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (TopCat.Sheaf.inverseImageRing f.base S.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlat (R := TopCat.Sheaf.inverseImageRing f.base S.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)
    (hq : QuasiIso q)
    (F : SheafOfModules.{u} (moduleRings S.toRingedSpace)) (i : ℤ) :
    Nonempty
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
          ((DerivedCategory.homologyFunctor _ i).obj
            (E ⊗ (derivedPullback f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
        (SheafOfModules.toSheaf
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf))).obj
          ((CochainComplex.mapBifunctor P
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (TopCat.Sheaf.inverseImageModule f.base S.sheaf F))
            (@curriedTensor _ _ (SheafOfModules.monoidalCategory
              (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i))
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison
--uses relativeTensorPullback_homology_comparison` finds the defining module and one
other module mentioning the declaration. The 413 transitive downstream modules keep
identical statements because the elaborated signature and the definitions it uses do not change.
No adaptation is necessary or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison | B4 | Private proved helpers and proof context; original signature identical. |
| Sheaf.AlgebraicGeometry.RelativeTorPullbackTensorLowerBound | unclaimed | Applies the same theorem with the same binders and conclusion; no edit. |

## Status

landed 20261013T131323-L-4033143 2026-10-13 (merge of deliver/B4/Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison)
