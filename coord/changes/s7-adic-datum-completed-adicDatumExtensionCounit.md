# AlgebraicGeometry.Scheme.adicDatumExtensionCounit

## Reason

The old definition repeatedly expands nested choices from the complete derived-change-of-rings specification. Package the universal scalar pair once as AdicDatumScalarPair, including its counit, universal property, triangulated structure and K-flat computation, and project its functor and counit. The existence theorem is proved from reductionDerivedExistence. This retains the same standard localizations and ordinary extension (completedConstantExtension and reductionChange are definitionally equal). The selected pair is determined up to the unique isomorphism compatible with its universal counit, so this does not select unrelated data or change the derived scalar-extension operation.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

The unclaimed consumer `Sheaf.Paper.CompletedFiniteReductionTensorComparison`
originally exceeded the 60-second compile limit against the changed dependency.
Its ordinary and derived tensor proofs now use `let E := reductionChange T φ`
in place of the definitionally equal completedConstantExtension alias. This aligns
the complex and homotopy maps with the exposed counit and avoids comparing their
large chosen functor presentations. Its tensor-left/right application also supplies
`(C := B)` explicitly, as recorded with adicDatumRing. No consumer signature changes.

## Old

```lean
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (completedConstantExtension T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  unfold adicDatumQh adicDatumExtension completedConstantExtension
  exact ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
      φ).choose_spec.choose_spec
    |>.choose_spec.choose_spec.2.2).choose_spec.choose
```

## New

```lean
def adicDatumExtensionCounit :
    adicDatumQh T R ⋙ adicDatumExtension T φ ⟶
      (reductionChange T φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        adicDatumQh T S :=
  (adicDatumScalarPair T φ).counit
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | Normalize the proof aliases to the same ordinary functor as this counit. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
