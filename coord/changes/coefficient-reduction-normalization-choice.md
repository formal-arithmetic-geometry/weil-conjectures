# WeilConjectures.coefficientNormalizedReductionNormalizations

## Reason

The original statement asserted the prescribed normalizations for every arbitrary
choice of three natural tensor isomorphisms in a core reduction record. The record
places no normalization constraint on those fields. Negating just finiteTensor
(and its inverse) in odd residual characteristic preserves the entire record,
its tensor subrecord, all projection formulas and its finite quotient calculus.
It changes the finite representative square on the nonzero coefficient unit.
Thus the old universal assertion is false. This is STATEMENT-DISPUTED, repaired
here by constructing the normalized comparison fields as the source does.

The replacement retains the entire CoefficientDerivedSystemReductionModel
subrecord. The proof also retains both projection identities by a record update.
Only the three unconstrained comparison fields change. Its sole consumer is
adapted to select the normalized record and transport the tensor-subrecord
equality and quotient calculus. That consumer's full declaration signature is
verbatim, and its original mathematical conclusion is preserved.

No target signature or definition used by a target changes. The independent
reader should check the corrected existential assertion against Stacks 07A4;
the change restores construction of canonical maps rather than claiming that
unconstrained isomorphisms are canonical.

## Old

```lean
theorem coefficientNormalizedReductionNormalizations
    (T : CoefficientDerivedSystemTensors l E W)
    (R : CoefficientDerivedSystemReduction l E W)
    (hRT : R.toCoefficientDerivedSystemTensors = T)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :
    CoefficientReductionTensorNormalization l E W R ∧
      CoefficientFiniteTensorNormalization l E W R ∧
      CoefficientEvaluationTensorNormalization l E W R ∧
      CoefficientReductionTensorEvaluation l E W R
```

## New

```lean
theorem coefficientNormalizedReductionNormalizations
    (R : CoefficientDerivedSystemReduction l E W) :
    ∃ S : CoefficientDerivedSystemReduction l E W,
      S.toCoefficientDerivedSystemReductionModel = R.toCoefficientDerivedSystemReductionModel ∧
      CoefficientReductionTensorNormalization l E W S ∧
      CoefficientFiniteTensorNormalization l E W S ∧
      CoefficientEvaluationTensorNormalization l E W S ∧
      CoefficientReductionTensorEvaluation l E W S
```

## Users

Read-only downstream.py --direct --uses and a whole-library name search identify
one external declaration user and direct importer. The full transitive import
closure also reaches many other modules, but none mentions the changed name.
The adapted consumer retains its signature and public imports verbatim.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientNormalizedReductionNormalizations | A9 | Construct comparison fields; retain the entire reduction-model subrecord. |
| Sheaf.Paper.CoefficientNormalizedReductionModels | unclaimed on the current server | Select S and transport the tensor equality and finite quotient calculus along the subrecord equality. |

## Status

landed 20261028T020149-L-2472700 2026-10-28 (merge of deliver/A9/Sheaf.Paper.CoefficientNormalizedReductionNormalizations)
