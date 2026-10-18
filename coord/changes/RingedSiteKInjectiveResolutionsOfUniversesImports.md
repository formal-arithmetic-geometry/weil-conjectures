# RingedSiteKInjectiveResolutionsOfUniverses imports

## Reason

The independent-universe theorem is now proved from the free-module/sheafification
adjunction, exactness transfer to abelian sheaves, and the generic source-library
K-injective replacement. The equal-universe theorem and extension-by-zero construction
are not used. Proof APIs are imported privately, as required by module visibility.
The existing public `Mathlib.Algebra.Category.Grp.AB` import is retained: a
focused consumer test demonstrated that privatizing it breaks downstream
instance elaboration; restoring it made all three affected test consumers compile.
No declaration signature, definition, universe, instance declaration, or target meaning
changes. The original theorem is the only declaration in this module.

## Old

```lean
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
```

## New

```lean
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
```

## Users

`tools/downstream.py` and `--uses` were run before the change. All transitive
importers are listed below. No user is adapted or requires a claim: the theorem's
signature is unchanged, and the import-pruning static check finds no use of a lost
declaration. The holder column records current claims at the time of this check;
no statement or proof belonging to another group is edited.
All 41 direct importers were compiled individually against the changed module
in a scratchpad consumer sandbox, in dependency order. All passed within
60 seconds each, including the tower modules and RGammaDerivedLimit. The
delivery compile, axiom probe, and static import-pruning check also passed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedCoinductionAdjunction | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses | E2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses | E3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | D3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction | E1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison | E2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | E3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ContinuousEtaleCohomology | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.EtaleGenericImmersionProjection | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport | B8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars | B9; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteRingEtaleCompactGenerators | G3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleCompact | G4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FiniteTorConstructibleEtaleGeneration | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.FormalClosedSupportAdjunction | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel | H2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.OpenBaseChangeSiteTransport | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex | C8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtale.SectionsConservative | D5; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleContinuousCohomologyLimit | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteLocallyProjective | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient | F7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalizationFilteredSection | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleUnitLerayChainFormula | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProEtaleWContractibleSectionsDerived | K3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.ProperHypercoverEtaleDescent | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPair | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.StrictConstantTowerOperations | J7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.StrictTowerOpenExtension | J8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows | J9; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | Y7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.UnboundedEtaleCohomologyAcyclicBasis | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | K7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.CompactSupportRoosCofinality | M8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.FlatRingedDiagramRestriction | J1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.LeftModuleDerivedEvaluationForget | P1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.ModuleRestrictionKernelComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses | J4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.RingedToposBinaryDescent | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.SiteAugmentationSpectralSequence | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.SiteTruncationDerivedLimit | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.Sites.RGammaDerivedLimit | R5; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization | A8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.StrictRoosComparison | B4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.CategoryTheory.StrictTowerArithmeticRestriction | R7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.AdicGlobalDerivedHom | D4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.AmbientIndDerivedSums | F5; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | F6; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.BrownHypothesesGeneration | E1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CoefficientHomRepresentativeEvaluation | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CoefficientHomZeroClass | V3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CoefficientRingedSequenceSite | V4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompactSupportExchangeTransport | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompactSupportReductionTower | F8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompactSupportSiteCoherence | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompactificationRefinementLocalizing | T9; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompleteResidueCohomologyBounds | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompletedPullbackAdjunction | M2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompletedRlimFunctor | M3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.CompletionMateComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | U6; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ConstantTowerTransition | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ConstructibleCompactness | U7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.DerivedAdjunctionShift | N1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ExactProductFunctorStrictLimit | J1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ExternalComparisonTriangles | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.FiniteFreeHomComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.FormalClosedSupportDerived | W5; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IndHeartKernelsCokernels | M3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralDerivedOperations | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralFinitePullbackComposition | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralHomReduction | M4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralHomReductionComparison | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | H7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.LocalizingClosureExistence | P1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | Q3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | K6; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProperOpenTowerComparison | Q4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProperUnboundedWindowBounded | C9; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ProperUnboundedWindowIso | F8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.PurityComparisonUnitInjectiveModel | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.RefinementExchangeCoherence | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.SfHomTriangulated | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.SiteHypercoverDerivedDescent | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.SitePerfectComplex | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.SmoothMateCounitCancellation | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.StratumAmbientHom | R4; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.StrictTowerOperations | Y2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.TateInverseLimitBaseChange | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.Paper.TorsionLimitSheafCompleteness | B7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | S1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | Z8; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.EtaleInternalHomDevissage | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.FlatModelGeneration | S3; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | M7; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.RingedLocalizationRHomOrthogonality | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctors.UnboundedClassicalTruncation | Y2; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | U1; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.ComparisonTruncatedCohomology | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.SimplicialPhEtaleSquare | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.TotalSiteDerivedComponents | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed; not adapted | Original theorem signature retained; no lost dependency declaration used. |

## Status

landed 20261018T145104-L-3641429 2026-10-18 (merge of deliver/J3/Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses)
