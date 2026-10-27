# WeilConjectures.RationalVerdier.completionChain

## Reason

The restored item does not compile within the single-file limit with the old nested
`Exists.choose_spec` projection. A diagnostic with 5,000 heartbeats fails during
kernel checking; reduction expands signed totalizations, quotient tensor towers and
chosen sheaf colimits. An inferred-type version has the same kernel timeout.

Reorder the three existential witnesses with Mathlib's `Exists.imp` and `exists_comm`
before choosing the cochain map. The new outer existential retains the entire
original predicate, including the tensor and model witnesses, quotient coordinates,
zero shifted coordinate, descended comparison and constructible invertibility.
Choosing its outer witness therefore selects a map with exactly the original
normalization. Local tensor generators and the two mapping-fiber coordinates
uniquely determine this map. This avoids kernel expansion through dependent choices
of the much larger tensor and representative witnesses. No import is added.

The residue-field inverse proof now rewrites only `map_natCast`, avoiding broad
`simp` search. Its result is an inverse of the same natural-number element; inverses
are unique. No target signature, hypothesis, conclusion, tensor object, evaluation
normalization or coefficient comparison equation changes. The target statement review
must check the preserved normalized completion interpretation because `Completion`
is used by `RationalVerdier.Conclusion`.

The transparency options keep ordinary definitions folded during elaboration.
They do not change existing data fields or export any instance attribute change.

## Old

```lean
@[instance_reducible] def units : ∀ x : X, Invertible (l : X.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D l hl).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) : IsUnit (l : X.residueField x)).invertible
```

```lean
def completionChain :
    constructibleTensorTotal l E X ⟶ integralOperationsTensorComplexFunctor l E X :=
  (@constructibleTensorCompletion l _ E _ _ _ X
    (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
    (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
    (units D l hl X)).choose_spec.choose_spec.choose
```

## New

```lean
@[instance_reducible] def units : ∀ x : X, Invertible (l : X.residueField x) :=
  fun x ↦ (show IsUnit (l : X.residueField x) from by
    have h := (finiteFieldDatumPrimeUnit D l hl).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x)
    rw [map_natCast] at h
    exact h).invertible
```

```lean
def completionChain :
    constructibleTensorTotal l E X ⟶ integralOperationsTensorComplexFunctor l E X :=
  (exists_comm.mp
    ((@constructibleTensorCompletion l _ E _ _ _ X
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
      (quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of D.k)))
      (units D l hl X)).imp (fun _ h ↦ exists_comm.mp h))).choose
```

## Users

The source scan `tools/downstream.py Sheaf.SixFunctors.RationalVerdier --uses units
completionChain` found 36 downstream modules. Only the item mentions `completionChain`;
`units` is an unchanged inverse of the same element. No consumer requires adaptation.
The table includes every downstream importer, together with the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.FiniteTorStability | E5 | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.GeometricOperations | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.PointTraceReconstruction | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RelativeKunneth | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | S4 | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | No adaptation; signatures and normalization preserved. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | No adaptation; signatures and normalization preserved. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | No adaptation; signatures and normalization preserved. |
| Sheaf.SixFunctors.RationalVerdier | H7 | Definition repair; existing signatures retained. |
| Sheaf.SixFunctors.WeilChosenDualityHom | D2 | No adaptation; signatures and normalization preserved. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No adaptation; signatures and normalization preserved. |

## Status

landed 20261025T041211-L-1080399 2026-10-25 (merge of deliver/H7/Sheaf.SixFunctors.RationalVerdier)
