# AlgebraicGeometry.Scheme.adicDatumModelDerivedNormalization

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumModelDerivedNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (adicDatumExtension T
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).obj
        (adicDatumModelReduction T d M b) ≅ adicDatumModelReduction T d M a :=
  letI := adicDatumComplexCounit_isIso T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
    (adicDatumExtension_kflat T (adicDatumProjection T d b) M.complex M.isKFlat)
  asIso (adicDatumComplexCounit T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)) ≪≫ adicDatumModelNormalization T d M a b h
```

## New

```lean
def adicDatumModelDerivedNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (adicDatumExtension T
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).obj
        (adicDatumModelReduction T d M b) ≅ adicDatumModelReduction T d M a :=
  letI := adicDatumComplexCounit_isIso T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)
    (adicDatumExtension_kflat T (adicDatumProjection T d b) M.complex M.isKFlat)
  asIso (adicDatumComplexCounit T
    ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)
    (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M.complex)) ≪≫ adicDatumModelNormalization T d M a b h
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
