# AlgebraicGeometry.derivedPullback

## Reason

The adopted source and local copy declare the same public functor and specification.
Their joint import fails with an environment-already-contains derivedPullback error
(as recorded for quarantined consumers). Replace the local existential choice with
the source canonical transported module-derived functor, and migrate all live reverse
import descendants atomically. The source tensor specification is fully proved and
uniqueness of left derived functors identifies this construction up to canonical
isomorphism with the old resolving-class construction. Both compute pullback on K-flat
resolutions. Target definition review is reopened; target statements are unchanged.
No WeilConjectures declaration, body, attribute or import is modified.

## Old

```lean
@[no_expose] noncomputable def derivedPullbackData {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  Classical.choose (exists_derivedPullback g)

/-- The derived pullback `L g^* : D(𝒪_S) ⥤ D(𝒪_T)`.

For `g : T ⟶ S`, this is the composite of termwise inverse image and derived change
of rings along `g^sharp`.  If `P ⟶ E` is any K-flat resolution, its canonical
representative is `g^*P = 𝒪_T ⊗_{g⁻¹𝒪_S} g⁻¹P`; the comparison isomorphisms supplied
by derived change of rings make this independent of `P`.
Source: literature/blueprint/master/blueprint/sec-picard-framework/
  sk-thm-picard-semicon/def-pc-derived-pullback.md, node def-pc-derived-pullback
  (blueprint: def-pc-derived-pullback). -/
noncomputable def derivedPullback {T S : Scheme.{u}} (g : T ⟶ S)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))] :
    schemeDerivedCategory S ⥤ schemeDerivedCategory T :=
  derivedPullbackData g
```

## New

The duplicate module is withdrawn. Every live consumer imports the adopted source,
which already provides:

```lean
noncomputable irreducible_def derivedPullback :
    schemeDerivedCategory.{u, w} S ⥤ schemeDerivedCategory.{u, w} T :=
  (schemeDerivedCategoryEquiv S).functor ⋙ Scheme.Modules.derivedPullback g ⋙
    (schemeDerivedCategoryEquiv T).inverse
```

Here `g : T ⟶ S` and the two shared `HasDerivedCategory.{w}` instances are the
section parameters, exactly as in the original signature. The source
`derivedPullback_spec` replaces the local theorem with the same clauses, using the
identically defined IsKFlatTensor and IsKFlatTensorResolution names. No equality
with an arbitrary existential choice is asserted for the new functor.

The complete module migration is listed below. Imports are redirected to source
counterparts only where needed to avoid colliding definitions. Source hypotheses
occasionally generalize the copied version (no properness/Noetherian assumptions for
the shifted unit, no Noetherian ring assumption for PerfectDescentOnOpen); no target
assumptions or conclusions are changed. Consumers requiring additional helpers keep
them under Sheaf, with complete existing proofs adapted to the canonical functor.

## Users

The original source-only downstream.py --uses derivedPullback check listed 34 textual
users in 38 live import descendants. On the repair base, OpenFlatComplexStalkCounit
is also live and is included below. The following table includes these reverse import
descendants and the item, a superset of those textual users. All were unclaimed at
inspection, except the assigned module held by B2. The delivery is reviewed as a
single interface migration. Quarantined files are preserved, with node replacement
arguments and source attachments supplied in this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackModuleModel | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackModuleModel |
| Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde |
| Sheaf.AlgebraicGeometry.AffineFreeLowestMatrixLocus | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.AffineKFlatPullbackChartComparison |
| Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedOpenPullbackHomology |
| Sheaf.AlgebraicGeometry.DerivedPullback | B2 | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullback |
| Sheaf.AlgebraicGeometry.DerivedPullbackComposition | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionAssocKFlat |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCoherence | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionCoherence |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionIsIso | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionIsIso |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackCompositionUnitKFlat |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitEquality | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatTensorModel | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackKFlatTensorModel |
| Sheaf.AlgebraicGeometry.DerivedPullbackRecordedComposition | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackRecordedComposition |
| Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorAssociativity | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorAssociativity |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorProduct | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct |
| Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedSingleOpenLocus |
| Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.DerivedTensorPreservesQCoh |
| Sheaf.AlgebraicGeometry.FlatTelescopeSumModels | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit |
| Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit | unclaimed | Redirect public and private imports to WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition; retain all signatures and proofs, using the adopted derivedPullback, tensorPullbackAdditive and counit |
| Sheaf.AlgebraicGeometry.OpenRestrictedRepresentativeData | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.OpenRestrictedRepresentativeData |
| Sheaf.AlgebraicGeometry.PerfectDerivedTensor | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PerfectDerivedTensor |
| Sheaf.AlgebraicGeometry.PerfectDescentOnOpen | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen |
| Sheaf.AlgebraicGeometry.PerfectHomCochainCounit | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PerfectHomCochainCounit |
| Sheaf.AlgebraicGeometry.PerfectHomComparisonTriangle | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.PerfectHomCompositionPrism | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.PerfectHomOpenTransportSquare | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PerfectHomOpenTransportSquare |
| Sheaf.AlgebraicGeometry.PerfectHomTransport | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionTailAbstract | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso | unclaimed | Adapt imports/API; retain additional definitions and complete proofs |
| Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.PullbackStalkTensorComparison |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackHomologyComparison |
| Sheaf.AlgebraicGeometry.RelativeTensorPullbackKFlatModel | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.RelativeTensorPullbackKFlatModel |
| Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition | unclaimed | Withdraw duplicate; replace by WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition |

Return C-20359 was an overlapping import-pruning change, not a mathematical
objection. This retry rereads the current affine module-model file and all
retained consumers, preserves the reviewed replacement by the adopted source,
and constructs the delivery on freshly fetched `sheaf-dag`. The independently
pruned imports are not restored in any retained consumer.

## Status

landed 20261020T163313-L-3724832 2026-10-20 (merge of deliver/B2/Sheaf.AlgebraicGeometry.DerivedPullback)
