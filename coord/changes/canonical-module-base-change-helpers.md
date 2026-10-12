# canonicalModuleBaseChange_iso_comparison helpers

## Reason

Add two intermediate public statements in their own modules for the original
coordinate-comparison proof. Existence is proved from the existing derived
counit; compatibility is a remaining strict geometric part. The original
statement and definitions are unchanged.

## Old

No helper declarations existed.

## New

```lean
theorem canonicalModuleBaseChange_iso_comparison_c0
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (_sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (_hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B) :
    let fA := f ≫ eS.hom
    let gA := eT.inv ≫ g ≫ eS.hom
    ∃ c0 : (derivedPullback (pullback.fst fA gA)).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G),
      IsDerivedModulePullbackComparison (pullback.fst fA gA) G c0
```

```lean
theorem canonicalModuleBaseChange_iso_comparison_ab
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (G : X.Modules)
    (c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G))
    (hc : IsDerivedModulePullbackComparison g' G c)
    {A B : Scheme.{u}} (eS : S ≅ A) (eT : S' ≅ B)
    (c0 : (derivedPullback (pullback.fst (f ≫ eS.hom)
      (eT.inv ≫ g ≫ eS.hom))).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings (pullback (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom)).toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback (pullback.fst (f ≫ eS.hom)
          (eT.inv ≫ g ≫ eS.hom))).obj G))
    (hc0 : IsDerivedModulePullbackComparison
      (pullback.fst (f ≫ eS.hom) (eT.inv ≫ g ≫ eS.hom)) G c0) :
  let fA := f ≫ eS.hom
      let gA := eT.inv ≫ g ≫ eS.hom
      let E := (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
      let T := schemeDerivedDirectImage eT.inv
      ∃ a : (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ≅
            T.obj ((derivedPullback gA).obj ((schemeDerivedDirectImage fA).obj E)),
        ∃ b : (schemeDerivedDirectImage f').obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback g').obj G)) ≅
            T.obj ((schemeDerivedDirectImage (pullback.snd fA gA)).obj
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings (pullback fA gA).toRingedSpace)) 0).obj
                  ((Scheme.Modules.tensorPullback (pullback.fst fA gA)).obj G))),
          (schemeDerivedBaseChangeMap f f' g g' sq.w E ≫
              (schemeDerivedDirectImage f').map c) ≫ b.hom =
            a.hom ≫ T.map
              (schemeDerivedBaseChangeMap fA (pullback.snd fA gA) gA (pullback.fst fA gA)
                pullback.condition E ≫ (schemeDerivedDirectImage (pullback.snd fA gA)).map c0)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparison | J3 | privately imports helpers; original signature unchanged |

These new names have no existing downstream users. No existing definition or
statement changes and no target review is reopened by a definition change.

## Status

landed 20261012T220522-L-1394068 2026-10-12 (merge of deliver/J3/Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeIsoComparison)
