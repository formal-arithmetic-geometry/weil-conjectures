# AlgebraicGeometry.Scheme.Modules.counitBaseChange_degreeZero_comparison

## Reason

Restore the zero-hole implementation quarantined by the cluster restore, as
assigned in coord/rework.tsv. The adopted library now also has
Scheme.Modules.derivedPullback, whereas the specified comparisons and shared
HasDerivedCategory.{w} instances use AlgebraicGeometry.derivedPullback.
Qualify all three occurrences in the statement and proof to retain the intended
functor and the independent universe w. No hypothesis, conclusion, comparison
construction, target signature or mathematical definition is changed.
The archived source fails at its signature lines 72 and 73: the selected
(derivedPullback g).obj expects DerivedCategory S.Modules, but receives
schemeDerivedCategory S, and (derivedPullback g').obj expects hom universe u
while E has the specified independent hom universe w. Compiling the qualified
version against the same current mate-square source succeeds in 8.3 seconds.

The original two public imports and the private mate-square import are retained.

## Old

Signature from the preserved quarantine archive:

```lean
theorem counitBaseChange_degreeZero_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M]
    (h0 : SheafOfModules.IsInvertible.{u, u, u}
      (((pushforward f).rightDerived 0).obj M))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr sq.w).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    ∃ (a : (pullback g).obj ((pushforward f).obj M) ≅
        H.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)))
      (b : H.obj ((schemeDerivedDirectImage f').obj ((derivedPullback g').obj E)) ≅
        (pushforward f').obj ((pullback g').obj M)),
      (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
        a.hom ≫ H.map (schemeDerivedBaseChangeMap f f' g g' sq.w E) ≫ b.hom
```

## New

```lean
theorem counitBaseChange_degreeZero_comparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g)
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M]
    (h0 : SheafOfModules.IsInvertible.{u, u, u}
      (((pushforward f).rightDerived 0).obj M))
    (hq : ∀ q : ℕ, 0 < q → IsZero (((pushforward f).rightDerived q).obj M)) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr sq.w).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    ∃ (a : (pullback g).obj ((pushforward f).obj M) ≅
        H.obj ((AlgebraicGeometry.derivedPullback g).obj ((schemeDerivedDirectImage f).obj E)))
      (b : H.obj ((schemeDerivedDirectImage f').obj
          ((AlgebraicGeometry.derivedPullback g').obj E)) ≅
        (pushforward f').obj ((pullback g').obj M)),
      (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
        a.hom ≫ H.map (schemeDerivedBaseChangeMap f f' g g' sq.w E) ≫ b.hom
```

## Users

The item is currently absent from lean/, so tools/downstream.py reports
unknown module. A search of lean/ and quarantine/ for both its module and its
declaration finds one actual consumer, listed below. The DAG parent
lem-pc-counit-base-change-is-iso also retains this dependency. The other DAG
mentions are ancestry or creation metadata of the existing comparison lemmas.
The consumer uses the intended shared-category comparison and requires no
adaptation. It remains under its separate quarantined rework assignment.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison | A5 | Restore and disambiguate the intended derived pullback in its statement and proof. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso | separate quarantined rework | Its existing application of the comparison retains the same binders and result; no adaptation. |

The original node attachment and all statement and proof dependencies remain.
Only the Lean statement record and restoration note are refreshed. No adopted
source module, other group's module, public instance or attribute is edited.

## Status

landed 20261021T022426-L-2845861 2026-10-21 (merge of deliver/A5/Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison)
