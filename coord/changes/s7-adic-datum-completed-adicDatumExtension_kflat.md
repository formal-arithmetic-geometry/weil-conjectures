# AlgebraicGeometry.Scheme.adicDatumExtension_kflat

## Reason

Normalize completedConstantExtension to the definitionally equal reductionChange,
as certified by adicDatumOrdinaryExtension_eq (rfl). The tensor-section abbreviation
uses the same sheafification map. This changes only the presentation of the statement;
its hypotheses and conclusion are judgmentally equal to the originals. No target
signature or adopted-source module changes. Target meanings using the associated
definitions reopen the usual statement review.

Adapt `Sheaf.Paper.IntrinsicCompletionCompleted` (unclaimed): the original
`rw [heq] at h` in `completedKoszulPowerSheaf_kflat` fails because `heq` is stated
using completedConstantExtension while the returned K-flat assertion uses
reductionChange. Replace the rewrite and final exact with
`simpa only [← adicDatumOrdinaryExtension_eq, heq] using h`. This changes only
the private proof and explicitly uses the definitional identification; all public
signatures and definitions of that consumer stay verbatim.

## Old

```lean
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((completedConstantExtension T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
```

## New

```lean
theorem adicDatumExtension_kflat (C : CochainComplex (completedConstantModules T R) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := R) C) :
    CochainComplex.IsAcyclicTensorKFlat (R := S)
      (((reductionChange T φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj C)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCoefficientDatumCompleted | S7 | Definitionally equal statement; included in the consumer check. |
| Sheaf.Paper.IntrinsicCompletionCompleted | unclaimed | Adapt the private K-flat rewrite to the equal scalar-functor presentation. |

## Status

landed 20261021T143948-L-29513 2026-10-21 (merge of deliver/S7/Sheaf.Paper.AdicCoefficientDatumCompleted)
