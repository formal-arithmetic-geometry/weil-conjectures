# Sheaf.Paper.ProperFiniteNormalization public imports

## Reason

The existing signatures use the canonical bounded-constructible comparison, identity
open normalization and coefficient comparisons. Keep their two public API modules and
remove redundant public and unused proof imports. The finite-ring origin theorem and
the new identity-open scalar lemma are imported privately for proofs. No declaration
signature, visibility, attribute, or existing definition body changes.

## Old

```lean
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.ClopenCommonCompactSupport
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.Paper.CompactificationCoherence
```

## New

```lean
public import Sheaf.Paper.ClopenCommonCompactSupport
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ProperFiniteNormalization | U2 | Own statements compile against the retained public APIs. |

A source search of both library roots found no current Lean imports of this module.
DAG parents remain attached and retain every declaration and its meaning; the module
is not withdrawn. No target statement or definition changes and no consumer adaptation
is needed.

## Status

landed 20261025T203326-L-2805184 2026-10-25 (merge of deliver/U2/Sheaf.Paper.ProperFiniteNormalization)
