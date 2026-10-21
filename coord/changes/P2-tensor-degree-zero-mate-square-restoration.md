# AlgebraicGeometry.Scheme.Modules.tensorDegreeZeroMateSquare

## Reason

Restore the entire quarantined zero-hole module recorded in coord/rework.tsv.
The original implementation fails against the adopted source: within Scheme.Modules,
unqualified derivedPullback now names Scheme.Modules.derivedPullback, whose derived
category morphisms live in universe u. The original theorem instead fixes shared
HasDerivedCategory instances with morphisms in the arbitrary universe w. The compiler
rejects the original at lines 71 and 73, reporting DerivedCategory.{w, u, u + 1}
where DerivedCategory.{u, u, u + 1} is expected.

Qualify the three statement occurrences and the corresponding proof occurrence as
AlgebraicGeometry.derivedPullback.{u, w}. This is the functor already specified by
IsDerivedModuleBaseChangeMap, the pinned left-derived counits, and the existing
TensorSingleBaseChangeSquare. All binders, hypotheses, ordinary and derived
comparisons, the conclusion and proof argument are preserved. The canonical
comparison is inverted only at the finite locally free source, never at the
base-change map. No mathematical definition, target or unit route changes.

## Old

The lean/ path is absent; its full implementation is preserved at
quarantine/Sheaf/AlgebraicGeometry/Picard/TensorDegreeZeroMateSquare.lean.

```lean
theorem tensorDegreeZeroMateSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [(tensorPullback (pullback.fst f g)).Additive]
    [HasInjectiveResolutions (Limits.pullback f g).Modules]
    (G : X.Modules) [((pushforward f).obj G).IsFiniteLocallyFree] :
    let M := (pushforward f).obj G
    let K := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0
    ∃ (e0 : (tensorPullback g).obj M ≅
        H.obj ((derivedPullback g).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M)))
      (φ : (derivedPullback g).obj K ⟶
        (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace)) 0).obj
            ((tensorPullback (pullback.fst f g)).obj G))),
      IsDerivedModuleBaseChangeMap f g G φ ∧
      moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition G =
        e0.hom ≫ H.map ((derivedPullback g).map (canonicalSingleDirectImageMap f G)) ≫
          H.map φ ≫ (canonicalDirectImageH0Iso (pullback.snd f g)
            ((tensorPullback (pullback.fst f g)).obj G)).hom
```

## New

```lean
theorem tensorDegreeZeroMateSquare
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [(tensorPullback (pullback.fst f g)).Additive]
    [HasInjectiveResolutions (Limits.pullback f g).Modules]
    (G : X.Modules) [((pushforward f).obj G).IsFiniteLocallyFree] :
    let M := (pushforward f).obj G
    let K := (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) 0
    ∃ (e0 : (tensorPullback g).obj M ≅
        H.obj ((AlgebraicGeometry.derivedPullback.{u, w} g).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj M)))
      (φ : (AlgebraicGeometry.derivedPullback.{u, w} g).obj K ⟶
        (schemeDerivedDirectImage (pullback.snd f g)).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings (Limits.pullback f g).toRingedSpace)) 0).obj
            ((tensorPullback (pullback.fst f g)).obj G))),
      IsDerivedModuleBaseChangeMap f g G φ ∧
      moduleBaseChangeMap f (pullback.snd f g) g (pullback.fst f g)
          pullback.condition G =
        e0.hom ≫ H.map ((AlgebraicGeometry.derivedPullback.{u, w} g).map
          (canonicalSingleDirectImageMap f G)) ≫
          H.map φ ≫ (canonicalDirectImageH0Iso (pullback.snd f g)
            ((tensorPullback (pullback.fst f g)).obj G)).hom
```

## Users

The downstream.py query reports unknown module because this item is quarantined.
A full import scan of lean/ and quarantine/, preferring the live version of a module,
finds one direct consumer and eighteen further transitive consumers. Every consumer
is quarantined and unclaimed at inspection. The sole direct call is
Modules.tensorDegreeZeroMateSquare p k G in PicardRankMatchDerivedTruncationData.
It needs the pinned shared-category comparison with arbitrary universe w, precisely
the restored interface. It introduces no new hypothesis or altered comparison.
All dependency edges, including the DAG parent, stay. No current live consumer or
other group's module needs adaptation; none is withdrawn. The quarantined consumers
remain independent rework assignments. No target statement is changed, and this
qualification does not change any definition a target uses.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare | P2 | Restore complete proof and intended shared-category interface. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed, quarantined | Direct consumer; intended comparison unchanged, no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed, quarantined | Transitive consumer; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed, quarantined | Transitive consumer; no adaptation. |

## Status

landed 20261021T022440-L-2847936 2026-10-21 (merge of deliver/P2/Sheaf.AlgebraicGeometry.Picard.TensorDegreeZeroMateSquare)
