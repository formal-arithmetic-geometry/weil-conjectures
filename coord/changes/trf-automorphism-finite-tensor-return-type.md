# WeilConjectures.trfAutomorphismFiniteTensor

## Reason

State the already inferred codomain explicitly as normalizedDVRModules.
The tensor construction and every argument are unchanged. This keeps its
coefficient category explicit when elaborating finite tensor evaluation.
The old and new codomains are definitionally equal.

## Old

```lean
def trfAutomorphismFiniteTensor (M : coefficientSequenceModules l E S) (n : ℕ) :=
  SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (trfAutomorphismFiniteCoefficientMap l E g n)
    ((trfAutomorphismFiniteRaw l E g n).obj
      ((coefficientSequenceEvaluation l E S n).obj M))
```

## New

```lean
def trfAutomorphismFiniteTensor (M : coefficientSequenceModules l E S) (n : ℕ) :
    normalizedDVRModules l E S n :=
  SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
    (trfAutomorphismFiniteCoefficientMap l E g n)
    ((trfAutomorphismFiniteRaw l E g n).obj
      ((coefficientSequenceEvaluation l E S n).obj M))
```

## Users

The item module has no downstream modules. Its finite-evaluation theorem is
the only user and is checked in the same compile.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.AutomorphismTensorReductionComparison | S1 | Definitionally identical tensor codomain and identical construction. |

## Status

landed 20261026T070924-L-3699055 2026-10-26 (merge of deliver/S1/Sheaf.TraceFormula.AutomorphismTensorReductionComparison)
