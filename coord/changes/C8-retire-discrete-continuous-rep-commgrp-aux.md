# Rep.discreteContinuousRep_equiv_with_compatible_objectwise_iso

## Reason

Retire the duplicate listed in coord/retire-items.tsv. The prerequisites have
already migrated to their upstream twins. The current Sheaf and upstream files
have byte-identical theorem docstrings, signatures and complete proof bodies.
The item has zero holes; this delivery removes the duplicate rather than claiming
a new proof. The adopted source library is unchanged.

The Sheaf file publicly imports EtaleFieldGsets and registers the two existing
forgetful instances globally. The upstream twin instead publicly imports
EtaleFieldGeometricAction and registers those same instances locally. Its sole
direct consumer already publicly imports EtaleFieldGsets and registers both
instances itself. Thus the one-line migration preserves every declaration,
public import and instance available to all downstream modules.

## Old

Declared in Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux:

```lean
theorem discreteContinuousRep_equiv_with_compatible_objectwise_iso
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    let D := DiscreteContinuousRep.{0, u, w} ℤ G
    let U : D ⥤ Rep.{w} ℤ G := ObjectProperty.ι _
    let V := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G)) ⋙
      ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
    ∃ E : CommGrp (DiscreteContAction (Type w) G) ≌ D,
      ∃ e : ∀ X, (E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
        (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).obj X ≅
          (CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).obj X,
      ∀ {X Y} (f : X ⟶ Y),
        ((E.functor ⋙ U ⋙ RepToAction ℤ G ⋙
          (CategoryTheory.forget (ModuleCat.{w} ℤ)).mapAction G).map f) ≫
            (e Y).hom = (e X).hom ≫
              ((CommGrp.forget (DiscreteContAction (Type w) G) ⋙ V).map f)
```

The sole direct consumer has:

```lean
import Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux
```

## New

Retain the identical signature and proof in WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrpAux.
Withdraw the duplicate with deleted.txt and redirect the existing node's Lean
attachment to the twin, with existing:true. In the direct consumer use:

```lean
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrpAux
```

No statement, definition, target, proof dependency or unit route changes. In
particular the theorem still applies to every carrier universe, arbitrary chosen
Cartesian structures, and non-Hausdorff topological groups. The component
isomorphisms and their naturality are the very same upstream result.

## Users

The complete current downstream closure from tools/downstream.py contains
28 modules. The sole textual user outside the item is the direct consumer;
only its private proof import changes. Its own public imports and global instance
registrations preserve the API of every indirect user.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModules | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesData | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.BaseFieldCohomologicalDimension | {"who": "C2", "t": 1792530675.4460924, "since": "2026-10-20T21:11:15Z"} | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryAnnihilator | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationCore | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleStalkContinuousCohomology | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ForwardEmbedding | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleUnitsH2ReverseEmbedding | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp | unclaimed | Replace the private proof import; retain its existing instance registrations, signature and proof. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | {"who": "H1", "t": 1792533696.5034637, "since": "2026-10-20T22:01:36Z"} | No edit; the consumer retains identical declarations, public imports and instance registrations. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No edit; the consumer retains identical declarations, public imports and instance registrations. |

The adapted direct consumer compiled on the project server in 2.0 seconds
with no warnings. tools/import_direction.py confirmed no import cycle.

## Status

landed 20261020T233111-L-893661 2026-10-20 (merge of deliver/C8/Sheaf.CategoryTheory.DiscreteContinuousRepCommGrpAux)
