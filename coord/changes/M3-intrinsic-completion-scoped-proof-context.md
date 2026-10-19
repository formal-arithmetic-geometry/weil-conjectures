# Sheaf.Paper.IntrinsicCompletionCompleted scoped proof context

## Reason

The preflight command scanner records the new section variables and section-local
transparency settings as a command/interface change. They support private abstract
monoidal and localization helpers, avoiding expensive elaboration through the concrete
sheaf tensor implementation. They are scoped to sections that end in this file.
No existing declaration signature, visibility, definition body, instance attribute,
or public import changes. In particular, none of the five target statements or
definitions used in their statements changes meaning.

## Old

The original nondeclaration commands, verbatim after comments are stripped:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
variable (X : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)
attribute [instance] completedKoszulConstant_additive
```

## New

The delivered nondeclaration commands, verbatim after comments are stripped:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
variable (X : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)
set_option backward.isDefEq.respectTransparency false
variable {M : Type*} [Category* M] [Preadditive M] [MonoidalCategory M] [MonoidalPreadditive M] (C D K L : CochainComplex M ℤ) [HomologicalComplex.HasMapBifunctor C K (curriedTensor M) (.up ℤ)] [HomologicalComplex.HasMapBifunctor C L (curriedTensor M) (.up ℤ)] [HomologicalComplex.HasMapBifunctor D K (curriedTensor M) (.up ℤ)]
attribute [instance] completedKoszulConstant_additive
set_option backward.isDefEq.respectTransparency false
```

The added `M`, category instances, complexes, and bifunctor instances belong only to
`section TensorUnits`; the second transparency setting belongs to `section Descent`.
Both sections end before the enclosing namespace ends. Private helpers cannot be
named by importers. The settings only guide proof elaboration in their sections.
The original top-level settings, variables and instance attribute stay unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntrinsicCompletionCompleted --direct --names`
was used to enumerate the direct consumers below. Since public signatures, public
imports and definition bodies are identical, every consumer sees the same declarations;
no consumer adaptation is necessary. Claim holders were not queried because no consumer
is edited. The independent reader may inspect these unchanged interfaces.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicSmoothBaseChange | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.BoundedConstructibleComplete | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CommonStageCalculus | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedCompactSupportExchange | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedDirectImageLimits | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedOpenExchangeTransport | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedPullbackReduction | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.CompletedPullbackTriangles | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.IntrinsicCompletion | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.ProperBaseChangeFourCorners | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.ReconstructionUniformTower | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.SbcCompletedOperations | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.UniformCompleteTriangulated | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | not queried; no adaptation | Public interface and definition data unchanged. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | not queried; no adaptation | Public interface and definition data unchanged. |

All indirect consumers likewise receive the same public interface. No adapted module
is included in this delivery. No target definition review is reopened by scoped proof
commands.

## Status

landed 20261019T192804-L-1868170 2026-10-19 (merge of deliver/M3/Sheaf.Paper.IntrinsicCompletionCompleted)
