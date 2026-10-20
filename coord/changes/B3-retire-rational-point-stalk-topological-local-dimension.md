# AlgebraicGeometry.ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt

## Reason

The item is listed for retirement in `coord/retire-items.tsv`. Its main theorem is
already proved with exactly the same signature in
`WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`.
The sole remaining direct importer is `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`;
it uses only `localDim_openEmbedding`, not the stalk comparison. Move that proved
helper unchanged into the consumer as a private theorem, remove its obsolete proof
import, and withdraw the duplicate module. The consumer was unclaimed when this
repair began. No adopted source-library file changes.

## Old

The duplicate item's main signature:

```lean
theorem ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (p (IsLocalRing.closedPoint k))) =
      topologicalKrullDimAt (p (IsLocalRing.closedPoint k))
```

Its public helper:

```lean
theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x)
```

The consumer imports:

```lean
import Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension
```

## New

The main theorem is supplied by the existing source-library module, with exactly
the signature above; the item's DAG `lean` record now points there. The source
module and its proof stay unchanged. A direct import and `#print axioms` check
compiled successfully and reported only `propext`, `Classical.choice`, `Quot.sound`.

In the sole consumer, with the original helper proof unchanged:

```lean
private theorem localDim_openEmbedding {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt x = topologicalKrullDimAt (f x)
```

The obsolete import is removed. The retired item is listed in `deleted.txt`;
no module in the delivery or library still imports it after this adaptation.
The helper remains a proved private part of the existing fibre-dimension argument,
not a new statement or proof obligation. Update that node's proof description to
record its new location. No target statement or definition changes meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension --uses
AlgebraicGeometry.ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt`
reported the following 55 transitive importers. Only the defining module mentions
the stalk theorem; the only helper caller is the direct consumer. Its public
imports and public signature stay verbatim, so further importers require no edits.
The adapted consumer compiles in 1.9 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBound | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.AffineLimitFibreDimensionBoundCore | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.DescendQuasiFiniteAffine | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphCoherence | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange | unclaimed | Remove the sole direct import; relocate its proved helper privately. Public theorem unchanged. |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.GenericFreeBlowup | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.GoodCurvesPreimageConstructible | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.LimitFibreDimensionBound | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.NodalCurveLCICriterion | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | Q5 | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.QuasiFiniteAffineEtaleThickeningDecomposition | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.RetrocompactBoundedFibreDimension | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.AlgebraicGeometry.StableModificationFinitePresentationSpread | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.CompactSupportStaircaseExpansion | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.DeltaRestriction | X9 | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.FiniteHorizontalShriekComposition | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.ProperOpenRefinementAdjointProjection | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.ProperOpenTowerDerivedUnit | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.Paper.UnboundedProperOpenInterchange | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.RingTheory.PowerPerturbationFibreDimension | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.BaseModificationComparisonFibreImage | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatAssociatedEquidimensional | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatFibreComponentClosureDimension | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatFibreFreeNeighbourhood | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.LocalQuasiFiniteProjection | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.NoIsolatedContractedFibreComponent | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.NodalOpenLocus | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.PureRelativeDimensionFiniteStage | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.RelativeDimensionBaseChange | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.ValuativeDominationEtaNormal | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |
| Sheaf.TraceFormula.WeakRelativeNoetherNormalization | unclaimed | Unchanged: the direct consumer keeps all public signatures and public imports. |

## Status

landed 20261020T145446-L-2397211 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension)
