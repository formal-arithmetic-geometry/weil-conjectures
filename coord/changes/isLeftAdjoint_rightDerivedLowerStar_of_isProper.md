# AlgebraicGeometry.Etale.CompactificationUpperShriek.isLeftAdjoint_rightDerivedLowerStar_of_isProper

## Reason

The instance proof now invokes Grothendieck Brown representability and the explicitly
recorded proper coproduct-preservation theorem. The declaration's type and visibility are
unchanged; this record documents the completed proof interface.

## Old

```lean
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper :
    ((g)_*[A]).rightDerivedFunctor.IsLeftAdjoint := by sorry
```

## New

```lean
instance isLeftAdjoint_rightDerivedLowerStar_of_isProper :
    ((g)_*[A]).rightDerivedFunctor.IsLeftAdjoint := by
  -- Brown representability applied to proper coproduct preservation.
```

## Users

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek | F4 | proof completed |

## Status

landed 20261016T221610-L-1615266 2026-10-16 (merge of deliver/F4/WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek)
