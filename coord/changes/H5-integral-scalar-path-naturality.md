# WeilConjectures.IntegralScalarExchange.left, rightTransformation and right

## Reason

The completed paths inferred large return types through derived coefficient choices.
The original right-path naturality proof elaborated quickly but kernel checking
exceeded 60 seconds (78.9 to 95.7 seconds in the theorem alone). Make both completed
paths' native source and target explicit. Construct the named `rightTransformation` from the three original factors and
canonical functor associators. Define `right` as its component and use the same
named transformation for its naturality, keeping the large scalar choices
behind a single typed declaration.
The scoped instance selection uses the canonical sheaf-module abelian structure
and gives `proEtaleRingModules_hasDerivedCategory` priority 4000 in the three
definitions and `rectangle_naturality`. This matches the instance in the actual
coefficient functors instead of the reduction-category wrapper selected at
priority 3000. Both instances return `HasDerivedCategory.standard`; their
category is definitionally the same. No exported instance registration changes.

The maps and their order are unchanged. The local `a` has exactly the data of
`completedChange`. At each object, whiskering gives respectively scalar pullback,
the image under geometric pullback of the coefficient comparison, and exchange.
The two functor associators have identity components, so identity laws recover
the old right-path formula. The left-path body is unchanged. Empty schemes,
identity squares and identity coefficient maps use the same categorical identities.
No target hypothesis, conclusion or mathematical meaning changes; target meaning
review can verify the displayed component computation.

## Old

```lean
def left {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
      ((exchange (completed l E) (completedPull_comp l E) c c' x g b sp sj).app M) ≫
    (comparison (completedChange l E F i) c').app ((pull (completed l E) x).obj M) ≫
    (image (completed l F) c').map ((scalarPull (completedChange l E F i) x).hom.app M)

def right {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :=
  (scalarPull (completedChange l E F i) g).hom.app ((image (completed l E) c).obj M) ≫
    (pull (completed l F) g).map ((comparison (completedChange l E F i) c).app M) ≫
    (exchange (completed l F) (completedPull_comp l F) c c' x g b sp sj).app
      ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)
```

## New

Each definition below is scoped by these commands:

```lean
attribute [local instance 4000] proEtaleRingModules_hasDerivedCategory in
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian in
```

The naturality theorem and all three definitions use the same scoped commands.
`rightTransformation` is new constructed data, not an assumption or existence choice;
it is attached to the existing node alongside the paths it realizes.

```lean
def left {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y')).obj
        ((pull (completed l E) g).obj ((image (completed l E) c).obj M)) ⟶
      (image (completed l F) c').obj ((pull (completed l F) x).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) :=
  (pbcDerivedExtend (completedCoefficientMap l E F i Y')).map
      ((exchange (completed l E) (completedPull_comp l E) c c' x g b sp sj).app M) ≫
    (comparison (completedChange l E F i) c').app ((pull (completed l E) x).obj M) ≫
    (image (completed l F) c').map ((scalarPull (completedChange l E F i) x).hom.app M)

def rightTransformation {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b) :
    image (completed l E) c ⋙ pull (completed l E) g ⋙
        pbcDerivedExtend (completedCoefficientMap l E F i Y') ⟶
      pbcDerivedExtend (completedCoefficientMap l E F i X) ⋙
        pull (completed l F) x ⋙ image (completed l F) c' :=
  let a : Change (completed l E) (completed l F) :=
    { map := completedCoefficientMap l E F i
      square := completedChange_square l E F i }
  let I := image (completed l E) c
  let G := pull (completed l E) g
  let P := pbcDerivedExtend (completedCoefficientMap l E F i Y')
  let A := pbcDerivedExtend (completedCoefficientMap l E F i Y)
  let H := pull (completed l F) g
  let B := pbcDerivedExtend (completedCoefficientMap l E F i X)
  let J := image (completed l F) c
  let K := pull (completed l F) x
  let L := image (completed l F) c'
  let α : I ⋙ G ⋙ P ⟶ B ⋙ K ⋙ L :=
    Functor.whiskerLeft I (scalarPull a g).hom ≫
      (Functor.associator I A H).inv ≫
      Functor.whiskerRight (comparison a c) H ≫
      (Functor.associator B J H).hom ≫
      Functor.whiskerLeft B
        (exchange (completed l F) (completedPull_comp l F) c c' x g b sp sj)
  α

def right {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (g : Y' ⟶ Y) (b : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare b c'.g c.g g)
    (sj : OpenImmersionSquare x c'.i c.i b)
    (M : DerivedCategory (scalarReductionSource l E X)) :
    (pbcDerivedExtend (completedCoefficientMap l E F i Y')).obj
        ((pull (completed l E) g).obj ((image (completed l E) c).obj M)) ⟶
      (image (completed l F) c').obj ((pull (completed l F) x).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) :=
  (rightTransformation l E F i c c' x g b sp sj).app M
```

## Users

`tools/downstream.py --uses left right` deliberately matches short suffixes.
Every resulting module is listed below. A whole-library search for
`IntegralScalarExchange` finds only this module and the direct importer listed
last: there is no other namespace opening, export, alias or qualified reference
to either completed path. Thus the other suffix hits refer to unrelated
`left`/`right` declarations, variables or fields. No consumer needs adaptation.
The generic `scalarLeft`/`scalarRight`, finite paths and strict-system paths
are unchanged. Claim holders are recorded from the current claim files.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | C3 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | H5 | Own definitions and naturality proof; no hypotheses changed. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfNormalizedRationalClosedComparison` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfNormalizedRationalWeilSquares` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | F2 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | P3 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | D3 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.VerdierHomChainComposition` | Q6 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | A4 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilPullbackFibreReturn` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | X6 | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCoefficient` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCompletion` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateDescent` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateFinite` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Textual suffix hit for another declaration or field; no use of these paths. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Direct importer; uses only `openInverse_isIso`, `openInverse` and `square`, which are unchanged. |

The complete proof compiled in 20.3 seconds. After removing all debugging
options, the changed module and unchanged direct consumer
`Sheaf.Paper.ZlFrameworkOpenExchange` both passed the remote compile
(`lcompile.py --all`, exit code 0). No consumer adaptation was required.

## Status

landed 20261026T001747-L-28172 2026-10-26 (merge of deliver/H5/Sheaf.Paper.IntegralScalarIsomorphismExchange)
