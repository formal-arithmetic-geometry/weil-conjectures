# CoefficientTateTwistData

## Reason

The remote single-file compile passed in 56.9 seconds, but the delivery compile
with declaration probes took 74.4 seconds and was refused. Profiling identified
about 40 seconds in kernel checking of CoefficientTateTwistData, expanding its
completed-coefficient and stage-category expressions while checking the record.
Use four transparent named family types in its fields. This is a definitionally
equal presentation of exactly the original four families. No target or mathematical
statement changes; no coefficient data is replaced or hidden behind a proof.

## Old

```lean
structure CoefficientTateTwistData (n : ℕ) where
  finite : ℤ → SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S (n - 1))
  integral : ℤ → SheafOfModules.{u + 1}
    (completedIntegralCoefficientSheafUnrestricted ℓ E S)
  rational : ℤ → rationalConstructibleCategory D ℓ hℓ E S
  algebraic : ∀ _F : Padic.FiniteCoefficientFields ℓ Ω, ℤ →
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S
```

## New

```lean
/-- The finite line-family type, named to keep coefficient record checking small.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientFiniteTwistFamily (n : ℕ) : Type (u + 2) :=
  ℤ → SheafOfModules.{u + 1} (integralCoefficientSheaf ℓ E S (n - 1))

/-- The integral line-family type, retaining the actual completed coefficient sheaf.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientIntegralTwistFamily : Type (u + 2) :=
  ℤ → SheafOfModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted ℓ E S)

/-- The rational line-family type, retaining the raw scalar localization.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientRationalTwistFamily : Type (u + 2) :=
  ℤ → rationalConstructibleCategory D ℓ hℓ E S

/-- The algebraic line-family type with its displayed finite coefficient index.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
def coefficientAlgebraicTwistFamily : Type (max v (u + 2)) :=
  ∀ _F : Padic.FiniteCoefficientFields ℓ Ω, ℤ →
    algebraicallyClosedConstructibleCategory D ℓ hℓ Ω S

/-- The four coefficient lines for all integer twists.
Source: blueprint order 1505 (blueprint: def-coefficient-twists-detailed). -/
structure CoefficientTateTwistData (n : ℕ) where
  finite : coefficientFiniteTwistFamily ℓ E S n
  integral : coefficientIntegralTwistFamily ℓ E S
  rational : coefficientRationalTwistFamily D ℓ hℓ E S
  algebraic : coefficientAlgebraicTwistFamily D ℓ hℓ S Ω
```

## Users

`tools/downstream.py Sheaf.Paper.CoefficientTwistsDetailed --uses
CoefficientTateTwistData coefficientTateTwists` found only the item module for
both names. There are no external consumers to adapt. All transitive importers
see definitionally equal field types and the same record and projection names.
The exported `coefficientTateTwists` body remains verbatim.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientTwistsDetailed | Z6 | Transparent field-type names; construction unchanged. |

## Status

landed 20261025T205059-L-3121003 2026-10-25 (merge of deliver/Z6/Sheaf.Paper.CoefficientTwistsDetailed)
