# AlgebraicGeometry.Scheme.adicDatumTensorSection

## Reason

Replace the expanded sheafification-unit definition by an abbreviation of reductionTensorSection. Both expressions are definitionally equal: the source helper uses the same sheafification unit and canonical equality transport from the same ordinary extension witness. This avoids unfolding the entire derived-change existence specification while using tensor formulas.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((completedConstantExtension T φ).obj M).val.obj U := by
  letI := HasDerivedCategory.standard (completedConstantModules T R)
  letI := HasDerivedCategory.standard (completedConstantModules T S)
  letI : Module (R.obj.obj U) (S.obj.obj U) :=
    Module.compHom (S.obj.obj U) (φ.hom.app U).hom
  unfold completedConstantExtension
  exact (eqToHom
    ((SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{t + 2, t + 1, t + 1, t}
        φ).choose_spec.choose M).symm)
      |>.val.app U
    (((PresheafOfModules.sheafificationAdjunction.{t + 1}
      (𝟙 ((adicLisseForget T).obj S).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1} φ M)).app U
          (s ⊗ₜ[R.obj.obj U] m))
```

## New

```lean
abbrev adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((reductionChange T φ).obj M).val.obj U :=
  reductionTensorSection T φ M U s m
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |
| Sheaf.Paper.FiniteFreeConstructibleScalarTransport | unclaimed | Its finiteFreeConstantTensor uses the identical normalized pure-tensor section; no signature, data, or source adaptation; unchanged consumer compiled in 3.8 seconds against this packet. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
