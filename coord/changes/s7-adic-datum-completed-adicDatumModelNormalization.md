# AlgebraicGeometry.Scheme.adicDatumModelNormalization

## Reason

The ordinary extension presentation is normalized to reductionChange, which selects the same tensor functor as completedConstantExtension (adicDatumOrdinaryExtension_eq is proved by rfl). The pure tensor section is the same sheafification unit. These are definitional identifications, so no hypothesis or conclusion changes.

The targets and their signatures are unchanged. Target statements using these definitions require the normal stage-2 semantic review after landing. No file under WeilConjectures is changed.

## Old

```lean
def adicDatumModelNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (completedConstantQ _).obj
      (((completedConstantExtension T
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((completedConstantExtension T (adicDatumProjection T d b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex)) ≅ adicDatumModelReduction T d M a :=
  (completedConstantQ _).mapIso
    ((adicDatumBalance T (adicDatumProjection T d b)
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).app M.complex ≪≫
        eqToIso (congrArg (fun ξ ↦
          ((completedConstantExtension T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.complex) (limit.w (adicLisseRingSystem T d.ideal) (homOfLE h).op)))
```

## New

```lean
def adicDatumModelNormalization {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (a b : ℕ) (h : a ≤ b) :
    (completedConstantQ _).obj
      (((reductionChange T
        ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((reductionChange T (adicDatumProjection T d b)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M.complex)) ≅ adicDatumModelReduction T d M a :=
  (completedConstantQ _).mapIso
    ((adicDatumBalance T (adicDatumProjection T d b)
      ((adicLisseRingSystem T d.ideal).map (homOfLE h).op)).app M.complex ≪≫
        eqToIso (congrArg (fun ξ ↦
          ((reductionChange T ξ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            M.complex) (adicDatumProjection_comp T d (op b) (op a) (homOfLE h).op)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Same scalar/tensor/limit operation; included in the consumer check. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
