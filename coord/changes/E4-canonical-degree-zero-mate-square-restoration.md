# AlgebraicGeometry.Scheme.Modules.canonicalDegreeZeroMateSquare

## Reason

Restore the quarantined zero-hole implementation recorded in coord/rework.tsv.
The archive fails at lines 88 and 231 because unqualified derivedPullback now
resolves to Scheme.Modules.derivedPullback: its morphisms have sort Type u,
where the specified shared-category comparisons require Type w.
Qualifying AlgebraicGeometry.derivedPullback throughout the statement and private
proof restores the original intended functor without changing its universes,
binders, hypotheses, ordinary mate, or pinned derived comparisons.
canonicalDirectImageH0Iso and its construction are retained verbatim.
No target statement, mathematical definition, or unit route changes.

The shared section parameter remains:

```lean
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
```

## Old

The signature in the preserved quarantined implementation:

```lean
theorem canonicalDegreeZeroMateSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g)
    [HasInjectiveResolutions X'.Modules] (M : X.Modules) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr h).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app
        ((pullback g).obj ((pushforward f).obj M))
    H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ k.hom ≫
        (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
      H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f M)) ≫
        H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫
        H.map ((schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M)) ≫
        (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom
```

## New

```lean
theorem canonicalDegreeZeroMateSquare
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (h : g' ≫ f = f' ≫ g)
    [HasInjectiveResolutions X'.Modules] (M : X.Modules) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0
    let c := (pullbackComp g' f).app ((pushforward f).obj M) ≪≫
      (pullbackCongr h).app ((pushforward f).obj M) ≪≫
      ((pullbackComp f' g).app ((pushforward f).obj M)).symm
    let k := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).app
        ((pullback g).obj ((pushforward f).obj M))
    H.map (canonicalSinglePullbackMap g ((pushforward f).obj M)) ≫ k.hom ≫
        (pullbackPushforwardAdjunction f').homEquiv _ _
          (c.inv ≫ (pullback g').map ((pullbackPushforwardAdjunction f).counit.app M)) =
      H.map ((AlgebraicGeometry.derivedPullback g).map (canonicalSingleDirectImageMap f M)) ≫
        H.map (schemeDerivedBaseChangeMap f f' g g' h E) ≫
        H.map ((schemeDerivedDirectImage f').map (canonicalSinglePullbackMap g' M)) ≫
        (canonicalDirectImageH0Iso f' ((pullback g').obj M)).hom
```

Only private proof imports are removed: the retired empty
Sheaf.AlgebraicGeometry.DerivedPullbackComposition and the redundant
WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage and
WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction. The latter two are
already public dependencies of the retained comparison/base-change imports.
All five original public imports remain verbatim.

## Users

The assigned item is absent from lean/, so tools/downstream.py reports
unknown module. Searching all Lean sources under lean/ and quarantine/ finds
three direct importers and the additional actual declaration users below.
All these consumers are quarantined with separate rework assignments. Their
intended shared-category interface remains identical; no adaptation is forced
by this restoration. Their own unqualified references may require the same
independent adopted-source repair. No consumer is withdrawn or edited here.
Explanatory docstring-only mentions do not use the interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | E4 | Restore both public declarations and complete private proof. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison | separate quarantined rework | Direct importer; ordinary mate square has unchanged intended type. |
| Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare | separate quarantined rework | Direct public importer; canonicalDirectImageH0Iso is unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap | separate quarantined rework | Direct public importer; canonicalDirectImageH0Iso is unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageUnitMorphism | separate quarantined rework | Uses unchanged canonicalDirectImageH0Iso. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | separate quarantined rework | Uses unchanged canonicalDirectImageH0Iso. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | separate quarantined rework | Uses unchanged canonicalDirectImageH0Iso. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective | separate quarantined rework | Uses unchanged canonicalDirectImageH0Iso. |

The DAG attachment, all statement/proof dependencies and the original proof
steps remain. Only lean.statement and its restoration metadata are refreshed.
No adopted-source module, other group's module, public instance, attribute or
public import is changed. The independent delivery reader reviews restoration.

## Status

landed 20261021T020118-L-2586079 2026-10-21 (merge of deliver/E4/Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare)
