# Canonical single-module compatibility statements

## Reason

Expose three independent compatibility identities needed by the degree-zero mate square:
a one-morphism adjunction transpose, a pullback-only composition identity, and the H⁰
normalization of a direct-image unit. Each is strictly a component of the existing argument.
The existing module's public definitions, statements, universes, and visibility stay identical.
Only proof imports and private proved helpers are added to that module.

## Old

These three modules and declarations did not exist. The item theorem had a whole-proof sorry.

## New

`Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose` adds:

```lean
theorem canonicalSingleAdjunctionTranspose {X S : Scheme.{u}} (f : X ⟶ S) (N : S.Modules) (M : X.Modules) (a : (pullback f).obj N ⟶ M) : (Classical.choose (exists_schemeDerivedAdjunction f (hAdd := (Classical.choose exists_derivedPullbackComposition) f) ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f) ((Classical.choose (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition))) f))).homEquiv _ _ (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) = (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map ((pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫ canonicalSingleDirectImageMap f M
```

`Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare` adds:

```lean
theorem canonicalSinglePullbackSquare {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g) (N : S.Modules) (M : X.Modules) (a : (pullback f).obj N ⟶ M) : let E := (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj N let c := (pullbackComp g' f).app N ≪≫ (pullbackCongr h).app N ≪≫ ((pullbackComp f' g).app N).symm let d := ((Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app E ≫ eqToHom (congrArg (fun k ↦ (derivedPullback k).obj E) h.symm) ≫ ((Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app E d ≫ (derivedPullback g').map (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) ≫ canonicalSinglePullbackMap g' M = (derivedPullback f').map (canonicalSinglePullbackMap g N) ≫ canonicalSinglePullbackMap f' ((pullback g).obj N) ≫ (DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map (c.inv ≫ (pullback g').map a)
```

`Sheaf.AlgebraicGeometry.Picard.CanonicalDirectImageH0Unit` adds:

```lean
theorem canonicalDirectImageH0Unit {X S : Scheme.{u}} (f : X ⟶ S) [HasInjectiveResolutions X.Modules] (M : X.Modules) : (DerivedCategory.homologyFunctor (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map (canonicalSingleDirectImageMap f M) ≫ (Functor.homologyRightDerivedFunctorObjSingleFunctorIso (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) M 0 ≪≫ (pushforward f).rightDerivedZeroIsoSelf.app M).hom = ((DerivedCategory.singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).app ((pushforward f).obj M)).hom
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | U3 | Uses the three new statements through private proof imports; its original public interface is identical. |

The new declarations have no pre-existing users. No module is adapted.

## Status

landed 20261012T163622-L-2788292 2026-10-12 (merge of deliver/U3/Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare)
