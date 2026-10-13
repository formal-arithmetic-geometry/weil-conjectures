# MvPolynomial.ideal_coefficients_monomial_membership

## Reason

The coordinate ideal membership criterion and its proof do not use quotient rings.
Remove the two inherited public quotient imports. The theorem signature and all definitions
are unchanged. Both direct importers already publicly import both removed modules themselves,
so the declarations available to downstream users remain the same.

## Old

```lean
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.MvPolynomial.Basic
```

## New

```lean
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.MvPolynomial.Basic
```

## Users

`tools/downstream.py --uses ideal_coefficients_monomial_membership` lists uses of the criterion.
The direct importers are the parent and coefficient-map modules. Each independently imports
both quotient modules,
so no adaptation is necessary; all its downstream imports retain the same visible declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PolynomialIdealCoefficientsMonomialMembership | M4 | Proof completed; unused imports removed |
| Sheaf.Paper.PolynomialIdealCoefficientsMonomial | unclaimed | No change; already imports both quotient modules |
| Sheaf.Paper.PolynomialIdealCoefficientsMonomialMap | unclaimed | No change; already imports both quotient modules |

## Status

landed 20261013T024040-L-3336397 2026-10-13 (merge of deliver/M4/Sheaf.Paper.PolynomialIdealCoefficientsMonomialMembership)
