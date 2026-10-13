# affineSpectrum_counit_square proof elaboration

## Reason

Local reducibility attributes let Lean recognize the same categories through the scheme,
homotopy, and derived-category wrappers while normalizing quotient identity components.
These attributes are local to the namespace and disappear at its end. Existing declaration
signatures, definitions and public imports are unchanged; downstream mathematical statements
therefore retain their meanings. This record accompanies the static tool's conservative
classification of attribute commands as interface changes.

## Old

No local reducibility attributes.

## New

```lean
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  Functor.mapHomologicalComplex HomotopyCategory Functor.mapHomotopyCategory
  HomotopyCategory.quotient DerivedCategory.Q DerivedCategory.Qh
  HomologicalComplexUpToQuasiIso.Qh
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare | A2 | proof elaboration only |
| Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalComparisonSquare | not adapted | unchanged signature and meaning |

The downstream --uses check found these two source users of affineSpectrum_counit_square.
No user requires an adaptation; local attributes do not escape the delivered namespace.

## Status

landed 20261013T190133-L-3213617 2026-10-13 (merge of deliver/A2/Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare)
