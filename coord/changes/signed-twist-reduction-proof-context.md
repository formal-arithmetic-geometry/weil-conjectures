# WeilConjectures.signedTwistReduction_comparison: proof context

## Reason

Preflight flags added module-context commands conservatively. The theorem statement and
public imports are verbatim unchanged. Private helpers require local reducibility and
instance-selection settings to compare the published coefficient presentations without
unfolding the completed inverse limit. No existing definition or mathematical interface
is changed. All downstream uses keep the same theorem type.

## Old

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local irreducible] WeilConjectures.scalarReductionExistence
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.sheafCompose
  SheafOfModules.unit PresheafOfModules.unit
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (S : Scheme.{u})
  [∀ x : S, Invertible (l : S.residueField x)]
```

## Users

`tools/downstream.py Sheaf.Paper.SignedTwistReductionComparison --uses signedTwistReduction_comparison`
reports six direct declaration consumers (including this module), listed below. Its 75
transitive module descendants need no change because all existing public signatures and
public imports are preserved. No downstream module is included or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed | unchanged signature and public imports; no adaptation |
| Sheaf.Paper.CanonicalTateComparisons | claimed | unchanged signature and public imports; no adaptation |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | unchanged signature and public imports; no adaptation |
| Sheaf.Paper.PointTateFiberComparisonData | unclaimed | unchanged signature and public imports; no adaptation |
| Sheaf.Paper.SignedTwistReductionComparison | claimed | unchanged signature and public imports; no adaptation |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | unchanged signature and public imports; no adaptation |

## Status

landed 20261025T204825-L-3016714 2026-10-25 (merge of deliver/Q4/Sheaf.Paper.SignedTwistReductionComparison)
