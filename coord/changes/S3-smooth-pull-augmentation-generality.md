# WeilConjectures.RationalSmoothPurityCanonical.smoothPullAugmentation_isIso

## Reason

The argument uses ordinary finite-Tor pullback completeness, which holds for any
separated, locally finite-type, quasi-compact morphism. It does not use the
relative dimension or the other fields of the purity setting. State this
stronger coefficient-level API before the relative-orientation section, so the
proof is checked with its actual parameters. The original smooth statement is
its specialization at `P.coefficients.l`, `P.extension`, and `f`; no extra
hypothesis is required. The existing `smoothPullToOrdinaryOnGood` construction
performs that specialization. No target statement changes.

## Old

```lean
theorem smoothPullAugmentation_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
```

## New

```lean
theorem smoothPullAugmentation_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : finiteTorConstructibleIntegral l E Y (DerivedCategory.Q.obj C)) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E f).app C))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalSmoothPurityCanonical | S3 | Specialize the general coefficient API in `smoothPullToOrdinaryOnGood`; its signature and map are unchanged. |

`tools/downstream.py --uses smoothPullAugmentation_isIso` lists only this module.
There is no external adaptation. All uses of smooth purity still have the same
coefficient field, morphism, finite-Tor hypothesis, and strict augmentation.

## Status

landed 20261026T070945-L-3715061 2026-10-26 (merge of deliver/S3/Sheaf.Paper.RationalSmoothPurityCanonical)
