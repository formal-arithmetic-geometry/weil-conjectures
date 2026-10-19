# Bounded-constructible geometric parameters and the unit-coherence consumer

## Reason

The completed tensor proof uses the declared geometric setting:
separated schemes of finite type over a field. The old `sorry` bodies caused Lean to omit
these section instances from the elaborated type of the monoidal closure instance.
The tensor proof now retains them. The source headers, coefficient restrictions, complex
predicates and conclusions are unchanged; the inferred parameters now agree with the
node's setting. This is an intermediate-interface correction, not a change to a target.

The earlier reviewed B2 reduction was rolled back after the global build found
`UpperStarUnitCoherence:250`: `cannot omit referenced section variable inst✝²`.
Naming the local instance binders identifies this as `LocallyOfFiniteType Z.hom`.
The unit on the bounded-constructible category now uses Z's geometric instances.
The private lemma `leftDerivedUpperStarComp_hom_app_unit_obj` must retain them.
Its proof remains the same ambient composition-coherence lemma. Every public declaration,
visibility attribute and written signature of this consumer is unchanged.

The direct-image and internal-Hom obligations remain unchanged, with their original
`sorry` bodies. This delivery adds no hole. The direct-image interface is unchanged.
The inferred type of `isMonoidalClosed_boundedConstructible` and the restricted
monoidal constructions also retain the same three geometry instances because those
types use the completed monoidal instance. Their written statements and mathematical
meaning in the declared finite-type setting are unchanged.
No definition of bounded constructibility, coefficient ring, ambient derived functor or
target statement changes. The functor constructions still restrict the same ambient
functors, and their finite-type contexts supply the retained proof parameters.
Target mathematical meanings remain the same in that setting; the independent review
should check this intermediate-interface correction explicitly.

## Old

The published baseline prints the following effective signatures (`#check @...`):

```text
AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible : ∀
  (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite) Ab) [inst : CategoryTheory.MonObj Λ]
  [inst_1 : CategoryTheory.IsCommMonObj Λ] {k : Type u_1} [inst_2 : Field k]
  (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) {ℓ : ℕ}
  [AlgebraicGeometry.ProEtale.CondensedRing.IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)],
  (AlgebraicGeometry.ProEtale.boundedConstructible (AlgebraicGeometry.ProEtale.condensedRingObj Λ X.left)).IsMonoidal
```

The original inferred internal-Hom closure signature was:

```text
AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible : ∀
  (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite) Ab) [inst : CategoryTheory.MonObj Λ]
  [inst_1 : CategoryTheory.IsCommMonObj Λ] {k : Type u_1} [inst_2 : Field k]
  (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) {ℓ : ℕ}
  [AlgebraicGeometry.ProEtale.CondensedRing.IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)],
  (AlgebraicGeometry.ProEtale.boundedConstructible
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ X.left)).IsMonoidalClosed
```

The consumer's original omit clause, verbatim:

```lean
omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom] [Fact ℓ.Prime] in
```

## New

Against the completed proof overlay, Lean prints:

```text
AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible : ∀
  (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite) Ab) [inst : CategoryTheory.MonObj Λ]
  [inst_1 : CategoryTheory.IsCommMonObj Λ] {k : Type u_1} [inst_2 : Field k]
  (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
  [AlgebraicGeometry.QuasiCompact X.hom] [AlgebraicGeometry.IsSeparated X.hom] {ℓ : ℕ}
  [AlgebraicGeometry.ProEtale.CondensedRing.IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)],
  (AlgebraicGeometry.ProEtale.boundedConstructible (AlgebraicGeometry.ProEtale.condensedRingObj Λ X.left)).IsMonoidal
```

The internal-Hom closure type uses that monoidal structure, so its inferred signature
also retains the geometry parameters:

```text
AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible : ∀
  (Λ : CategoryTheory.Sheaf (CategoryTheory.coherentTopology Profinite) Ab) [inst : CategoryTheory.MonObj Λ]
  [inst_1 : CategoryTheory.IsCommMonObj Λ] {k : Type u_1} [inst_2 : Field k]
  (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
  [AlgebraicGeometry.QuasiCompact X.hom] [AlgebraicGeometry.IsSeparated X.hom] {ℓ : ℕ}
  [AlgebraicGeometry.ProEtale.CondensedRing.IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)],
  (AlgebraicGeometry.ProEtale.boundedConstructible
      (AlgebraicGeometry.ProEtale.condensedRingObj Λ X.left)).IsMonoidalClosed
```

The consumer retains the Z instances and omits only the still-unused ones:

```lean
omit [Fact (ringChar k).Prime] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [Fact ℓ.Prime] in
```

No other line in this consumer changes.

## Users

Source search: `python3 tools/downstream.py
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
--uses isMonoidal_boundedConstructible`.
The instance name occurs explicitly only in their defining module; the remaining uses are by
instance synthesis. The table includes every current transitive consumer (refreshed 2026-10-19). Their existing
finite-type contexts supply the retained geometry. The verification copies are compiled as
single files, with the freshly compiled core functor chain; they are not delivered.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleHomOfPreserves | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorHomAdjunctionOfPreserves | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | G9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | P9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | M3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | X6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor | A9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | C9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | H9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | Y5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian | J9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit | D9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleTorsionStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | E7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicClosedConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicResidueLissePerfectLift | V6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicStratifiedPerfect | P5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficientTwists | Z6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeart | X8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartSmall | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportReductionTower | P2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedERealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstantModelTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleSingleDegreeComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | N4 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedNakayama | U6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | T3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedNakayamaResolution | U1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DiagonalTowerSystem | W6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | X6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | R2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | N1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleLocalMonodromyRealization | U9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalCoefficientComparison | V9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteComparisonLocalizing | V7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | V8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.FiniteExceptionalSystemAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteFieldExceptionalPreservation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | U3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteProperBaseChange | U4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteTorInternalHomAnyField | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupport | Q9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | V8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | V4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralCriterionReductions | X3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralModels | D4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralModelsOperations | N1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Paper.IntegralStratumExtBound | K1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorProduct | N3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorPullback | J2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorShriek | F2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.KummerAdditivity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseCompletedSystemComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MateOpenRestriction | U2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | A5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | W5 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | B4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | D2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProjectionSectionNormalization | X7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityConventions | X8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityGysinStructure | F1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Z5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalStalkExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheafSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ResidueLisseProjectiveModels | G2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RestrictionLocal | R3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SectionDerivedRealization | J8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfPreservationClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | M9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothMateCounitCancellation | G4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityCoefficientTowers | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | C9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityCompactProjectionBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityNormalizedTowers | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerEvaluationAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerRightExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerRightExtensionFiniteColimits | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.StratifiedLattice | M6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwConventions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UnboundedLocalizingPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtRational | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VerdierExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WContractibleCondensedScalarEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilCompactSupportCohomology | A8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | Q6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FieldTensor | N1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteCompactProetale | A2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FlatModel | K7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FlatModelGeneration | E9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | T1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ModuleMapmodPullbackKFlat | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ScalarSixPullback | U6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Topology.ProfinitePointSite | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| TargetsCheck | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Retain the three Z geometry instances in one private omit clause; all public signatures unchanged. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.Statement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same mathematical statements and functors in the existing finite-type context; retained geometry supplied by instance synthesis. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| module | unclaimed | effect |

| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |

| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |

| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.ConstructibleSingleDegreeComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Finite-type contexts provide the retained geometry parameters; no source edit. |

## Status

landed 20261019T093325-L-2295338 2026-10-19 (merge of deliver/D3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)
