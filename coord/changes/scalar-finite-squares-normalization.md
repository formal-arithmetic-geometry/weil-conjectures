# AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.scalar_finite_squares

## Reason

The old hypotheses constrain the finite comparison and all four reduction maps but never
constrain the completed comparison `b`. The quotient conclusion does depend on `b`.
For identity pullback, equal coefficient fields, an odd prime and a free rank-one complex
in degree zero, replacing the normalized comparison by its negative preserves all five
old hypotheses. Its composite with the nonzero canonical quotient changes sign, so the
asserted quotient square cannot hold for both choices. The source argument assumes the
completed comparison is normalized. The parent `scalar_finite_model` already assumes
exactly `CompletedFormula`; the split omitted it.

Restore that hypothesis, prove the corrected theorem, and supply the parent's existing
`hb` at its only call. No definition or target statement changes. The correction is to a
false auxiliary split, and preserves the source statement of the parent and every target.

## Old

```lean
theorem scalar_finite_squares
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (hF : FiniteFormula l E L ι g bfin)
    (hL : LeftQuotientFormula l E L ι g vleft)
    (hR : RightQuotientFormula l E L ι g vright)
    (hTL : LeftTransitionFormula l E L ι g tleft)
    (hTR : RightTransitionFormula l E L ι g tright) :
    QuotientSquare l E L ι g b bfin vleft vright ∧
    TransitionSquare l E L ι g bfin tleft tright
```

## New

```lean
theorem scalar_finite_squares
    (b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
      (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g)
    (bfin : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ finiteLeft l E L ι g n ≅
          (integralOperationsGoodComplex l E Y).ι ⋙ finiteRight l E L ι g n)
    (vleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (vright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (tleft : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedLeft l E L ι g n)
    (tright : ∀ n : ℕ,
        (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g (n + 1) ⟶
          (integralOperationsGoodComplex l E Y).ι ⋙ restrictedRight l E L ι g n)
    (hb : CompletedFormula l E L ι g b)
    (hF : FiniteFormula l E L ι g bfin)
    (hL : LeftQuotientFormula l E L ι g vleft)
    (hR : RightQuotientFormula l E L ι g vright)
    (hTL : LeftTransitionFormula l E L ι g tleft)
    (hTR : RightTransitionFormula l E L ι g tright) :
    QuotientSquare l E L ι g b bfin vleft vright ∧
    TransitionSquare l E L ι g bfin tleft tright
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismScalarFiniteSquares | T2 | Assigned item; corrected hypothesis and complete proof of both squares. |
| Sheaf.Paper.IsomorphismScalarFiniteModel | unclaimed | Pass its existing `hb` before `hF`; all public signatures stay identical. |

The item has exactly one direct importer, `Sheaf.Paper.IsomorphismScalarFiniteModel`,
which is also the only other module mentioning `scalar_finite_squares`. The only change
to that importer is its proof argument. Its downstream importer
`Sheaf.Paper.IsomorphismScalarTensorKFlatModel` sees an identical parent signature.

## Status

landed 20261027T234320-L-97398 2026-10-27 (merge of deliver/T2/Sheaf.Paper.IsomorphismScalarFiniteSquares)
