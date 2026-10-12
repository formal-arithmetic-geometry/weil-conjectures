# Canonical degree-zero comparison interfaces

## Reason

Add explicit canonical comparison morphisms and the single missing compatibility square
needed to prove counitBaseChange_degreeZero_comparison. Every existing declaration's
signature and visibility is unchanged. No existing module besides the item is adapted.
The new modules have no existing external users.

## Old

The three new modules and their declarations did not exist. The existing item has its
original unchanged theorem statement and a whole-proof sorry.

## New

### Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

The shared section parameter is:
```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

```lean
abbrev canonicalTensorPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) : (tensorPullback f).Additive
```

```lean
def canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) : (derivedPullback f).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ⟶ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj ((pullback f).obj M)
```

```lean
theorem isIso_canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] : IsIso (canonicalSinglePullbackMap f M)
```

### Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison

The shared section parameter is:
```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

```lean
def canonicalSingleDirectImageMap {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) : (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj ((pushforward f).obj M) ⟶ (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)
```

```lean
theorem isIso_canonicalSingleDirectImageMap {X S : Scheme.{u}} (f : X ⟶ S) [HasInjectiveResolutions X.Modules] (M : X.Modules) (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) : IsIso (canonicalSingleDirectImageMap f M)
```

### Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare

The shared section parameter is:
```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

```lean
def canonicalDirectImageH0Iso {X S : Scheme.{u}} (f : X ⟶ S) [HasInjectiveResolutions X.Modules] (M : X.Modules) : (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M)) ≅ (pushforward f).obj M
```

```lean
theorem canonicalDegreeZeroMateSquare {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g) [HasInjectiveResolutions X'.Modules] (M : X.Modules) : let E := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M let H := DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0 let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫ (pullbackCongr h).app ((pushforward f).obj M) ≪≫ ((pullbackComp f' g).app ((pushforward f).obj M)).symm let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app ((pullback g).obj ((pushforward f).obj M)) H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ k.hom ≫ (pullbackPushforwardAdjunction f').homEquiv _ _ (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) = H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f M)) ≫ H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫ H.map ((schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M)) ≫ (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison | Q2 | New proof uses the three new comparison modules; existing signature unchanged. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | new in this delivery | Its square uses the real canonical maps constructed by the other two modules. |

There are no existing users of the new declarations. Existing importers of the item
see its two original public imports and the identical theorem signature.

## Status

landed 20261012T135306-L-1687425 2026-10-12 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison)
