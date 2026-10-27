# WeilConjectures.CompactSupportFiniteProjection.fixedComponent

## Reason

Converting the native bifunctor evaluation of the canonical projection to its expanded
support/tensor endpoints at concrete ModuleCat coefficients repeatedly unfolds large
derived tensor constructions. The original finite-stage proof exceeded 120 seconds;
small conversion probes took about 30 seconds in tactics and another 40–50 seconds in
kernel checking. The same coordinate conversion, performed at an arbitrary coefficient
category with its structure instances as parameters, has proved equality and IsIso APIs
whose combined tactic time is about 26 ms and kernel time about 157 ms in the diagnostic
probe. The definition now uses that generic coordinate evaluation directly.

This is a real refactor of the data construction, not an added existence witness or a
changed projection formula: the generic equality theorem identifies the helper with the
same counit/open-inverse projectionMapOfCompactification. The old fixedComponent signature,
all public imports and all existing declaration attributes stay verbatim. No hypothesis,
conclusion, first-input Tor requirement or structure-map separatedness condition changes.
Construction was unclaimed when checked; its direct fixedComponent consumer is currently
held by V5. No source-library module is edited.

The definition is in the targets' dependency closure, so its semantic review reopens under
AGENTS.md §4. The coordinate equality supplies the mathematical comparison for that review;
all Challenge signatures are preserved.

## Old

```lean
def fixedComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    ((fixedTensor (C := C) (E := E) (n := n) Y).obj
      ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj K)).obj L ⟶
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      (((fixedTensor (C := C) (E := E) (n := n) X).obj K).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  ((AlgebraicGeometry.ProEtale.projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) c).app K).app L
```

## New

The following proved generic interface is added in the same Sheaf module and attached to
its existing definition node def-sf-constructible-projection-mates:

```lean
/-- Evaluate the proper/open projection with its tensor-coordinate endpoints exposed.
Doing the endpoint conversion at an arbitrary coefficient category prevents repeated
reduction of derived tensor constructions after specializing the coefficients.
Source: the canonical proper/open mate, current projection-formula construction
(blueprint: def-sf-constructible-projection-mates). -/
def projectionTensorCoordinateComponent (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    ((AlgebraicGeometry.ProEtale.derivedTensor A Y).obj
      (((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor).obj K)).obj L ⟶
      ((AlgebraicGeometry.ProEtale.openImmersionLowerShriek A c.i).mapDerivedCategory ⋙
        (AlgebraicGeometry.ProEtale.lowerStar A c.g).rightDerivedFunctor).obj
        (((AlgebraicGeometry.ProEtale.derivedTensor A X).obj K).obj
          ((AlgebraicGeometry.ProEtale.upperStar A f).leftDerivedFunctor.obj L)) :=
  ((projectionMapOfCompactification A c).app K).app L

/-- The tensor-coordinate evaluation inherits invertibility of the published mate.
Source: the same proper/open projection (blueprint: def-sf-constructible-projection-mates). -/
theorem projectionTensorCoordinateComponent_isIso (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A))
    (h : IsIso (((projectionMapOfCompactification A c).app K).app L)) :
    IsIso (projectionTensorCoordinateComponent A c K L) := by
  exact h

/-- The coordinate presentation evaluates the published projection, without a new choice.
Source: the same proper/open projection (blueprint: def-sf-constructible-projection-mates). -/
theorem projectionTensorCoordinateComponent_eq (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [ProEtale.UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    projectionTensorCoordinateComponent A c K L =
      ((projectionMapOfCompactification A c).app K).app L := by
  rfl
```

The finite component calls it directly:

```lean
def fixedComponent {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left)
    (K : DerivedCategory (Sheaf (ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)))))
    (L : DerivedCategory (Sheaf (ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))))) :
    ((fixedTensor (C := C) (E := E) (n := n) Y).obj
      ((sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj K)).obj L ⟶
    (sfFixedCompactSupport (Padic.coefficientExtensionRing C.l E n) c).obj
      (((fixedTensor (C := C) (E := E) (n := n) X).obj K).obj
        ((fixedDerivedPull (C := C) (E := E) (n := n) f).obj L)) :=
  letI := Padic.finite_coefficientExtensionRing C.l E n hn
  projectionTensorCoordinateComponent
    (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))) c K L
```

## Users

The table includes all 117 transitive consumers printed by tools/downstream.py --uses,
its two direct occurrences, and the item being proved. Each existing statement retains
its meaning because the same canonical proper/open mate is evaluated.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | S3 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | T1 | Uses the generic coordinate API to prove the finite laws. |
| Sheaf.Paper.CompactSupportProjectionFormula | C3 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | T2 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Definition refactor and proved generic API; existing signatures, imports and meaning preserved. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | X3 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PairingData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Direct consumer of fixedComponent; compile original against the repaired definition; no adaptation planned. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeProductFactorSquaresCore | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.RelativeProductProperCompatibilityCore | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | F2 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TensorHomCoefficientTransposes | P3 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TowerPurityRealizedTranspose | D3 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.VerdierHomChainComposition | Q6 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | A4 | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Transitive consumer; no direct fixedComponent occurrence; existing interface and meaning preserved. |
| Sheaf.Paper.FiniteProjectionCompactificationTransport | T1 (new) | New coherence consumer; unchanged component interface, compiled against the refactored construction. |
| Sheaf.Paper.FiniteProjectionCompositionTransport | T1 (new) | New coherence consumer; unchanged component interface, compiled against the refactored construction. |

Validation: `lcompile.py --all` compiled both changed modules, the two new
coherence modules, and the unchanged `Sheaf.Paper.ProjectionFormulaCoherence`
consumer against the refactored definition (exit code 0). The consumer needs no
adaptation and is not part of the delivery. Final files contain no profiler settings.

## Status

landed 20261026T024025-L-631712 2026-10-26 (merge of deliver/T1/Sheaf.Paper.CompactSupportProjectionFiniteStages)
