# AlgebraicGeometry.Scheme.adicDatumModelReduction

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumModelReduction {K : adicDatumDerived T d} (M : AdicDatumModel T d K) (n : ℕ) :=
  (completedConstantQ _).obj
    (((completedConstantExtension T (adicDatumProjection T d n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
```

## New

```lean
def adicDatumModelReduction {K : adicDatumDerived T d} (M : AdicDatumModel T d K) (n : ℕ) :=
  (completedConstantQ _).obj
    (((reductionChange T (adicDatumProjection T d n)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
