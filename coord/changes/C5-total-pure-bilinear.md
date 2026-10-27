# total and totalPure

## Reason

Use the existing coefficient total-tensor functor and its homogeneous generator.
These are definitionally equal to the original KFlatTotalTensorModel aliases and
summand-injection formula. Keeping the existing construction named avoids repeatedly
unfolding the sheafification colimit while composing with the scalar total comparison.
Private equality proofs were checked by `rfl` for both aliases. The existing public
`RingedDerivedTensorNative` import already reexports the canonical coefficient tensor API. There are no current
Lean importers of this module; its DAG parents and attachment remain in place.

## Old

```lean
abbrev total (P Q : CochainComplex (Modules A) ℤ) :=
  (KFlatTotalTensorModel.total A).obj (P, Q)

/-- A homogeneous local generator of the actual direct-sum total tensor.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def totalPure (P Q : CochainComplex (Modules A) ℤ)
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    ((total P Q).X n).val.obj W :=
  (CochainComplex.ιMapBifunctor P Q (KFlatTotalTensorModel.tensor A) p q n h).val.app W
    (ringedComparisonPure A (P.X p) (Q.X q) W x y)
```

## New

```lean
abbrev total (P Q : CochainComplex (Modules A) ℤ) :=
  (WeilConjectures.coefficientTotalTensor.{u, u, u} J A).obj (P, Q)

/-- A homogeneous local generator of the actual direct-sum total tensor.
Source: Stacks 07A4 (blueprint: lem-pur-quotient-operation-adjoint-factorizations). -/
def totalPure (P Q : CochainComplex (Modules A) ℤ)
    (p q n : ℤ) (h : p + q = n) (W : Cᵒᵖ)
    (x : (P.X p).val.obj W) (y : (Q.X q).val.obj W) :
    ((total P Q).X n).val.obj W :=
  WeilConjectures.coefficientTensorGenerator.{u, u, u} J A P Q p q n h W x y
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientOperationAdjointFactorizations | C5 | Definitionally equal aliases; statement unchanged. |

The table includes every user listed by `tools/downstream.py --uses total` and
`--uses totalPure`. No target statement changes. The definitions retain exactly
their mathematical meaning, including the coproduct injections and signed differential.

## Status

landed 20261025T002454-L-3110664 2026-10-25 (merge of deliver/C5/Sheaf.Paper.QuotientOperationAdjointFactorizations)
