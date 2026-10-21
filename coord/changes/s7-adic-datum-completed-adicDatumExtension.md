# AlgebraicGeometry.Scheme.adicDatumExtension

## Reason

The old definition repeatedly expands nested choices from the complete derived-change-of-rings specification. Package the universal scalar pair once as AdicDatumScalarPair, including its counit, universal property, triangulated structure and K-flat computation, and project its functor and counit. The existence theorem is proved from reductionDerivedExistence. This retains the same standard localizations and ordinary extension (completedConstantExtension and reductionChange are definitionally equal). The selected pair is determined up to the unique isomorphism compatible with its universal counit, so this does not select unrelated data or change the derived scalar-extension operation.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose
```

## New

```lean
def adicDatumExtension :
    completedConstantDerived (completedConstantModules T R) ⥤
      completedConstantDerived (completedConstantModules T S) :=
  (adicDatumScalarPair T φ).functor
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteLevelRectangle | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.ProperBaseChangeFourCorners | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
