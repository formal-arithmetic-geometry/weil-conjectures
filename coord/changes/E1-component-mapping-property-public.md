# AlgebraicGeometry.ProEtale.component_mapping_property

## Reason

Repair the returned delivery at 3276ed0e4c9. The item duplicated the existing
`component_mapping_property`, but that theorem was private and could not be imported.
Expose the existing fully proved helper in its current Sheaf module, remove the duplicate,
and call it from the item. The source module is unclaimed in the current claim records.
No existing public theorem statement, definition, instance or public import changes.
No target statement or definition changes, so target statement review need not reopen.

## Old

```lean
private theorem component_mapping_property (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x)) :
    (∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x)) ∧
    ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w
```

## New

```lean
theorem component_mapping_property (T : Scheme.{u}) [IsAffine T]
    (F : Over (affineComponentSpace T) ⥤ T.ProEt)
    (p : ∀ E : Over (affineComponentSpace T), C((F.obj E).left, E.left))
    (hF : ∀ E : Over (affineComponentSpace T),
      (∀ x : (F.obj E).left, IsIso ((F.obj E).hom.stalkMap x)) ∧
      ∃ h : (F.obj E).left ≃ₜ
          {z : T × E.left | ConnectedComponents.mk z.1 = E.hom z.2},
        (∀ x, (h x).val.1 = (F.obj E).hom x) ∧ (∀ x, (h x).val.2 = p E x)) :
    (∀ (E : Over (affineComponentSpace T)) (x : (F.obj E).left),
      E.hom (p E x) = ConnectedComponents.mk ((F.obj E).hom x)) ∧
    ∀ (W : Over T) (E : Over (affineComponentSpace T)) (g : C(W.left, E.left)),
      (∀ w : W.left, E.hom (g w) = ConnectedComponents.mk (W.hom w)) →
      ∃! m : W ⟶ (Scheme.ProEt.forget T).obj (F.obj E),
        ∀ w : W.left, p E (m.left w) = g w
```

The proof is verbatim unchanged. A source/proof docstring is added for the now-public
helper; no new mathematical assertion or proof hole is introduced.

## Users

`python3 tools/downstream.py Sheaf.Paper.ComponentRelativeProfiniteSite --uses
component_mapping_property` finds 74 transitive importers and only one current textual
user: the declaring module itself (declaration and existing call). The item is the new
second caller. The table records every transitive importer and its current claim holder.
Only the declaring module and the item are changed. Existing callers keep identical types;
public import lists are unchanged. The original private name was unavailable to importers,
so no consumer requires repair. Compile both delivered modules through `lcompile.py --all`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ComponentLiftBaseChange | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ComponentLiftLisseSectionComparison | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ComponentRelativeProfiniteSite | unclaimed | Expose the existing proved helper; its type and proof are unchanged. |
| Sheaf.Paper.CondensedLocalizationHom | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ContinuousQbarLisseHeartClosure | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterDegreeZeroData | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterEvaluationCoherence | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterEvaluationData | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterMatrixCoordinates | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterRelativeMaps | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.FreeParameterScalarMaps | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerBarResolution | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerLocalSource | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerRefinement | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerResolutionColumns | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerScalarRestriction | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerStratumChart | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.KummerTermMate | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.PointPullbackDerivedHom | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ProfiniteConstantDerivedFunctions | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.ProfiniteDerivedEvaluation | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.RelativeComponentLiftPullbackSpace | E1 | Replace the duplicate helper with the existing theorem. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.RootTowerCoordinateFace | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.StratifiedDualizableBounded | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.WContractibleComponentDerivedHom | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.WStrictCommonComponentHypercovers | unclaimed | No change to existing declarations or imports; no adaptation needed. |
| Sheaf.Paper.WStrictLisseComponentCohomology | unclaimed | No change to existing declarations or imports; no adaptation needed. |

## Status

landed 20261023T131513-L-2115634 2026-10-23 (merge of deliver/E1/Sheaf.Paper.RelativeComponentLiftPullbackSpace)
