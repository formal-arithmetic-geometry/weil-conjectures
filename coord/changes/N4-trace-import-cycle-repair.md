# TraceBaseChangeFirst import-cycle repair

## Reason

Repair of returned delivery bd6e535e9b4 (N4, 2026-10-25 20:43 UTC).
The item now reaches TraceBaseChangeFirst through IntegralDirectImageReductionCone,
NormalizedScalarRestrictionPush, the scalar-pullback normalization data,
SectionDerivedRealization, SectionDerivedTensorData and ProEtaleSectionModuleFunctors.
The trace module's unused import of the higher BoundedConstructible theorem closes
an import cycle because that theorem imports the item.

The trace module is unclaimed. Remove its unused high-level import, retaining every
existing public declaration, signature and global attribute. Its only constructibility
predicate is constantModelBoundedConstructible, supplied by the already imported
CondensedConstantConstructibility module.

An import-only compile took 70.3 seconds. Sequential profiling identifies repeated
construction of internal-module tensor and derived-category structures, and repeated
normalization of a tensor structure chosen from unique existence. Use the existing
compact structure aliases from IntegralResidueDerivedMonoidal, make large construction
helpers locally irreducible, and construct the specified tensor core directly.

The old proved condensedTensorCore_eq identifies the chosen core with precisely the
canonical core used now. Likewise the old proved derived_unit_explicit identifies the
old explicit unit composite with exactly leftDerivedTensorUnitIso used now. Thus both
objects keep their mathematical meaning. The existence-and-uniqueness theorem remains
proved and unchanged. No arbitrary witness or new choice is introduced.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
```

```lean
def traceDegreeZeroUnitIso : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  F.leftDerivedFunctorIsoMapDerivedCategory.app (𝟙_ _) ≪≫
    F.mapDerivedCategoryFactors.app (𝟙_ _) ≪≫
    DerivedCategory.Q.mapIso
      (((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app (𝟙_ _)) ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso
          (Functor.Monoidal.εIso F).symm)
```

```lean
def condensedTensorCore : (upperStar Λ f).CoreMonoidal :=
  (condensedTensorCore_existsUnique Λ f).exists.choose
```

```lean
instance condensedUpperStarMonoidal : (upperStar Λ f).Monoidal :=
  (condensedTensorCore Λ f).toMonoidal
```

## New

Remove the unused high-level import. The existing private import of
Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
becomes public because the new public construction bodies refer to its unit isomorphism
and ordinary monoidal instance. This adds no import-graph edge. Keep the signatures and
attributes of these constructions, and use these bodies:

```lean
def traceDegreeZeroUnitIso : F.leftDerivedFunctor.obj (𝟙_ _) ≅ 𝟙_ _ :=
  F.leftDerivedTensorUnitIso
```

```lean
def condensedTensorCore : (upperStar Λ f).CoreMonoidal :=
  Functor.CoreMonoidal.ofOplaxMonoidal (upperStar Λ f)
```

```lean
instance condensedUpperStarMonoidal : (upperStar Λ f).Monoidal :=
  monoidal_upperStar Λ f
```

The old proved condensedUpperStarMonoidal_eq identifies this canonical structure with
the previous CoreMonoidal-to-Monoidal round trip. The unit and ordinary monoidal
equality proofs become reflexive. Redundant transports
in ordinary_upperStar_braiding and upper_comp_monoidal are removed. The now unused
proved private helpers monoidal_core_roundtrip, proof_transport_three,
condensedTensorCore_eq, generic_derived_delta, generic_derived_braid_Qh and
canonical_derived_symmetry are removed;
project-wide source search finds no other users. A proved private helper
condensedTensorCore_normalization exposes the same normalization equations without
expanding the choice term; lower_mu_pi uses it. Four existing compact aliases for
abelian, monoidal and derived structures are registered locally, and the module closed
structure,
transported coefficient multiplication and pullback-from-point constructions are locally
irreducible. The composition calculation uses the existing API with pullback and
composition constructions folded, and folds the right-adjoint lax structure after its
tensor equation has been proved. The previous local transparency override for this
section is removed. These select the same structures and add no global instances or
attributes. The localization functor Qh is folded locally, as is
residueDerivedMonoidal after its unit and tensor equations have been proved. The
three tensorator identifications in derived_trace_assembly use the proved private
residue_derived_tensor equation. Backward definition rules are disabled by default
and retained in the ordinary-braiding section that explicitly enables them.

Reuse the proved source-library theorem
`Functor.leftDerivedFunctor_map_braiding_hom_δ` from
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure`.
Both derived monoidal structures have tensor comparison leftDerivedTensorComparison,
so its equation is exactly the required residue-derived equation after simplifying
leftDerivedFunctorMonoidal_δ. The lax equation follows by inversion as before. This
removes the local K-flat calculation and its heavier private import of
Etale.Derived.UpperStarMonoidal.Braided. Remove the now unused direct private
LeftDerivedFunctor.Counit import as well; it is already publicly imported by the
existing LeftDerivedFunctor.Monoidal interface. The two ordinary pullback instances occur
before those tensor calculations, with identical signatures, attributes and canonical data.

A later dry run rejected the trace compile at 75 seconds despite its earlier standalone
54.1-second pass. Profiling isolated expensive failed rewrite searches in the concrete
composition calculation. Its tensor-quotient rewrite now acts only on the right-hand
side. The triangle-identity tensor cancellation is supplied by a proved generic private
lemma, tensorEndomorphisms_identity, instead of searching the concrete expression with
definitional rewriting. The module tensor structure remains folded after the ordinary
tensor normalization calculation, including during the abstract module assembly.
Sequential elaboration avoids rebuilding the same structures in parallel proof tasks.
Natural-transformation composition is kept folded, and the composition tensor equation
is opened with Functor.LaxMonoidal.comp_μ. The large trace propositions are folded before
the derived assembly and explicitly opened at the proof that needs their definitions.
These changes preserve all constructions and add no proof obligation.
The next dry run reached 61 seconds. The assembly therefore reuses the existing proved
DerivedCategory.symmetricCategory, whose underlying braiding is braidedCategory'.
The latter is kept locally folded after the public braiding alias is defined. The
private reconstruction of its symmetry proof is unnecessary; the original monoidal
functor instances and their derived braided proof fields remain in place.

Profiling also identifies repeated searches for colimit conditions on graded module
objects. Eight proved private caches supply the existing Grothendieck, flat-resolution,
tensor-colimit and graded-tensor instance proofs. Their instance attributes are scoped
only around private proof declarations. They cannot enter public signatures or public
definition bodies. The module adjunction is locally irreducible during ordinary tensor
normalization, where its explicit unit API is used. This version passed in 47.2 seconds;
the unused commutativity binder of the Grothendieck cache is then explicitly omitted.
The resulting final three-file build passes without warnings, rebuilding the adapted
trace module and both unchanged consumers in dependency order.

Every existing signature, visibility and resulting global attribute is preserved.
No adopted source-library module is changed. The two supporting import removals from
the earlier packet remain necessary and have their own change records.

## Validation

The static import-pruning check passes. The overlaid source import graph has no closing
cycle. Every existing public declaration and global attribute is retained; all four
delivery modules have zero `sorry` bodies. Exact `#check @...` comparisons of eighteen
public declarations match the published originals, including implicit parameters and
universes. These include the derived category, operation aliases, canonical comparisons
and final theorem.

The item passes its standalone check in 46.9 seconds and the integral coefficient square
in 24.1 seconds. The final three-file build passes the compile gate without warnings:
TraceBaseChangeFirst, then the unchanged ProEtaleProjectionExchangeMaps, then the
unchanged TraceBaseChangeSecond. It writes fresh artifacts in dependency order, so both
consumers are checked against the adapted trace constructions. No consumer adaptation
is needed. The temporary unchanged consumer copies and signature probe are removed.

Initial scratch checks used the published library rather than the sandbox overlay and
are not the final consumer evidence. An individual overlay check of TraceBaseChangeSecond
hit a kernel mismatch while using an older compiled intermediate; rebuilding that
intermediate and its consumer in the final set resolves it without source edits.

Current main changed ProEtaleSectionModuleFunctors during validation so it no longer
imports TraceBaseChangeFirst. Its obsolete snapshot is not included or adapted. The
trace import repair is retained because it removes the edge reported in bd6e535e9b4,
independently of that changing parent path. The consumer table was refreshed afterward.

## Users

The table lists the transitive source consumers returned by `tools/downstream.py`, plus
the adapted module. Declarations and mathematical meanings are identical. The static
import-pruning checker passes. The global build verifies downstream elaboration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | F7 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedHomChainRealization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ProjectiveDiagonalComposition | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalP1AmbientComposites | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalP1DiagonalTensor | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same public interface; unused import removed; equal canonical constructions and proved source braiding |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.VerdierHomChainComposition | Q6 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | A4 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.PoincareDuality.ConstructibleSheafBiduality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SecSmoothPurity.MixedBaseChange | C8 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | P2 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralKernelContractions | D4 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralKernelTateComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralKernelUnitCounit | Y6 | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ProperOpenCoefficientLeftTranspose | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ProperOpenCoefficientRightTranspose | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarCompositeModelPasting | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarDenseRefinementSquare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarProperOpenInterchangeSquare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarRefinementClosureSquare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SixFunctors.ScalarSixDirectImage | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Targets.PoincareUncurry | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Same declarations and meanings; no adaptation required by this change |
| TargetsCheck | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ClopenLowerShriek | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.Statement | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Additivity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.BaseChangeCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.BorelMoore | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.CoefficientMorphism | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.CompactCohomology | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.CompactPullback | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Correspondence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.CorrespondencePair | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.CurvePieces | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Dualizing | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FibreCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FibreModel | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FixedPoint | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FixedPointScheme | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Frobenius | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.FrobeniusLocalTerm | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.GenericQuotient | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.HomologyUnit | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.KunnethVerdier | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.LefschetzVerdier | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.LocalTerm | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.LocalTermLocality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Main | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ModelExtension | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.OpenPieceCoherence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.OpenSquare | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.PointNormalization | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Product | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ProperCompatibility | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ProperCurve | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ProperPushforward | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ProperPushforwardKernel | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.PullbackFamily | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.RelativeFrobenius | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.RelativeFrobeniusComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.RelativeFrobeniusIterate | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ShriekTraceFunction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ShriekTraceFunctionBaseCases | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ShriekTraceFunctionDevissage | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.ShriekTraceFunctionInduction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Stalk | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.SupportedPairing | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.TraceClass | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.TraceClassAdditivity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.WeilBaseChange | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.WeilSheafUpperStar | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same declarations and meanings; no adaptation required by this change |
| WeilConjectures.ZetaFunction.WeilObjectComparison | unclaimed | Same declarations and meanings; no adaptation required by this change |

## Status

Open; independent review required.
