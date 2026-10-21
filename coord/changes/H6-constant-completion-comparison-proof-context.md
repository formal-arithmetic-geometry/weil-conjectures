# CategoryTheory.ConstantCompletion comparison proof context

## Reason

Prove the existing finite scalar, strict reduction tower, derived scalar pullback,
and finite pullback comparisons using the prescribed ordinary comparisons and K-flat
computations. All existing public signatures, public definition bodies, and public
imports stay unchanged. New private helpers prove descent and extensionality through
homotopy localization. Local attributes prevent unfolding of derived and scalar data.
The already proved quotient presentation is checked through a generic continuation
and a module-sheaf specialization with an abstract tower functor.

## Old

The four existing theorem bodies are `by sorry`:
`finiteDerivedComparison`, `derivedReductionTowerComparison`,
`derivedPullComparison_existsUnique`, and `finitePull_existsUnique`.
The pre-existing local attribute after `derivedPull` is:

```lean
attribute [local irreducible] derivedPull
```

The original private generic tower construction internally chooses `ordinaryUnit`'s
unique projection formula. The public ordinary unit and quotient presentation definitions
are unchanged by this delivery.

## New

All four theorem signatures are unchanged. Their proofs descend the ordinary comparisons
using the invertible computation counits on the flat-term K-flat resolving class.
The derived scalar comparison is a natural transformation; only its target computation
counit needs to be invertible. The other three comparisons are natural isomorphisms.

New private proved helpers include `resolving_nat`, `resolving_nat_ext`,
`resolving_comparison`, `resolving_iso`, `resolving_comparison_iso`,
`resolving_square`, `resolving_square_iso`, `resolving_finite_comparison`,
`restricted_kFlat`, `module_flat_kFlat_resolution`, `restricted_flat`,
`resolving_tower_square`, `basechange_flat_kFlat`, `pull_flat_kFlat`,
`change_flat_kFlat`, `resolving_module_square`, and `resolving_module_square_iso`.
No private helper enters a public definition body or signature.

The generic tower construction now accepts the given ordinary unit and its proved
projection formula as arguments. This removes the old private `towerOrdinaryUnit`
construction and changes only the private `derived_tower_presentation` interface;
all its callers in this module are adapted. A scan of both library roots finds
no references to either private name outside this module. `derived_tower_presentation_cps` and
`module_tower_presentation` transport its fully proved existence witness to the unchanged
public quotient-presentation record. `ordinaryUnit_spec` supplies the existing chosen
unit's projection equation.

The new local irreducibility settings are:

```lean
attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.symmetricCategory CochainComplex.IsAcyclicTensorKFlat
  CochainComplex.IsKFlatIndependentCoefficients
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] dres change
attribute [local irreducible] derivedPull pull change
attribute [local irreducible] dres
```

The additional `dres change` and `dres` settings are enclosed in proof sections.
Single-theorem backward-definitional-equality options permit the generic representative
formulas to match their specializations. No consumer reducibility attribute changes.
The six added imports are private proof imports, listed in report.md.

The private `module_tower_presentation` proof additionally reconstructs its existing
abelian instance with the existing sectionwise preadditive parent explicit. This is
definitionally the original instance and avoids unfolding the transferred abelian
structure during concrete tower conversion. Two duplicate irreducibility attributes
were removed from later proof sections. No public signature or construction changes.

The quotient-presentation proof and the private derived-limit restriction proof
also expose the same existing preadditive parents in locally bound abelian
structures. These are definitionally equal reconstructions inside theorem proofs;
no exported instance or definition is changed. The complete variant compiled in
55.1 seconds through the approved compile tool.

## Users

The item belongs to H6. A read-only direct-import scan found the following consumers.
Their public interface and mathematical meaning stay unchanged; none is adapted.
Claim holders are immaterial to this proof-only change and are not asserted below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | H6 | Four comparison proofs and private proof checking helpers. |
| Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude | not queried; no adaptation | Public interface unchanged. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | not queried; no adaptation | Public interface unchanged. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicPerfectModelCompleteReduction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicPullbackPresentationTransport | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicResidueLiftComparisons | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicStratifiedPerfectData | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicStratumCompletionUnit | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.AdicStratumCoverConservativity | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedConstantAlgebraFlatQuotients | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedConstantCoefficientEquivalence | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedConstantPresentationTransport | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedExtensionZeroComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedKoszulConstantTransport | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedMapReduction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedPullbackAdjunction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedPullbackReduction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletedPullbackUnitTower | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CompletionMateComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.CondensedERealization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantCompletionUnitNormalization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantDirectImagePreservesComplete | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantInverseImageSection | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantPullbackScalar | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantReductionsFiniteProjectiveModel | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ConstantScalarDirectImageCompleteness | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.DerivedFiniteQuotientCoherence | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.DiagonalTowerLimit | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ExactCompletedKoszulPullback | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.ExactPullbackDerivedAdjunction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.FiniteTateSiteDescent | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.IntegralModels | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.IntegralTensorPullback | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.PulledReductionNormalizationComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.QuotientTowerEvaluationComplex | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.RationalDirectImageRealization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.RationalRealizationTensorComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.RationalThickEvaluation | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SbcCompletedOperations | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SfLocalizationAllStages | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.StratumCompletionUnitRestriction | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.StrictQuotientDiagonalNormalization | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.StrictQuotientScalarBalancing | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.StrictQuotientScalarBalancingData | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.WContractibleConstantReductionsML | not queried; no adaptation | Public interface unchanged. |
| Sheaf.Paper.WholeTowerIntegralPullbackComparison | not queried; no adaptation | Public interface unchanged. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | not queried; no adaptation | Public interface unchanged. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | not queried; no adaptation | Public interface unchanged. |
| Sheaf.SixFunctors.OpenFactorCoherence | not queried; no adaptation | Public interface unchanged. |

## Status

landed 20261021T203525-L-3809623 2026-10-21 (merge of deliver/H6/Sheaf.Paper.ConstantCompletionEquivalence)
