# WeilConjectures.AmbientPullbackTensor.pure

## Reason

The ambient pure-section abbreviation and the independent-size ordinary comparison
used definitionally equal sheafification constructions through different constants.
Converting the resulting generator equations after specializing to the selected
pullback repeatedly unfolds that functor. Use the independent-size constructor
in the ambient abbreviation, and explicitly retain its original ordinary-tensor
output type. Both constructions send the sectionwise tensor through the
sheafification unit and the inverse tensor/sheafification comparison. No scalar
factor, naturality condition or flatness condition changes. The target statements
remain verbatim; targets depending on this definition require renewed statement
review of the equivalent representation. The main module is held by Y9.
A universal Lean `rfl` probe checked equality with the original
`SemilinearSections.tensorSection` for arbitrary schemes, either site choice,
modules and sections. Both unchanged consumers compiled against the revised interface.

## Old

```lean
abbrev pure (X : Scheme.{t}) (s : Option ℕ) :=
  tensorSection.{t + 1, t, u} (topology X s) (coefficients ell E X s)
```

## New

```lean
abbrev pure (X : Scheme.{t}) (s : Option ℕ) :=
  fun (M N : Modules ell E X s) (U : (Site X s)ᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) ↦
    (tensorSectionAtSize.{t + 1, t, max u (t + 1)}
      (topology X s) (coefficients ell E X s) M N U x y :
        (tensor ell E X s M N).val.obj U)
```

## Users

The downstream search matches the short name `pure`; most rows refer to other
namespaces. Their statements are unchanged. The two consumers of
`tensorData_existsUnique` retain its normalization projection order and require
no edits. No other module is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AmbientPullbackTensorCoherence | Y9 | Uses the same canonical pure section with its original output type. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.CondensedCompactSupportProjection | V9 | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.EtaleSystemImageTensor | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.EtaleSystemTensorEvaluation | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | C6 | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | unclaimed | Uses the unchanged flat-representative consequence of normalized tensor data. |
| Sheaf.Paper.IntegralExpressionSystemComparison | unclaimed | Uses the unchanged flat-representative consequence of normalized tensor data. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SecSmoothPurity.ProEtaleCoefficientTowerNormalization | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed | Unrelated short-name match; no statement changes. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed | Unrelated short-name match; no statement changes. |

## Status

landed 20261026T071609-L-3954447 2026-10-26 (merge of deliver/Y9/Sheaf.Paper.AmbientPullbackTensorCoherence)
