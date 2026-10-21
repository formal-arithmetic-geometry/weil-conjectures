# AlgebraicGeometry.Etale.etaleSupportMapCompatibility

## Reason

The proof needs the monoidal notation namespace, the existing derived braiding, and
stable elaboration of the derived functor API. Preflight conservatively classifies
these added commands as a visible module change. Every attribute below is local;
no exported instance, attribute, notation or declaration signature changes.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local instance] derivedBraidedCategory
attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  upperStar lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
```

## Users

All entries are from `tools/downstream.py`. No consumer adaptation is necessary:
these commands affect elaboration only inside the item module. The original public
imports, existing definitions, and theorem signature stay verbatim. Current
holders are listed from the read-only claim records below.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence | T8 | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothAdjunctionData | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothGammaNormalization | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothPurityMaps | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothSiteRealizations | no active claim found | no interface change; no adaptation |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | no active claim found | no interface change; no adaptation |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | no active claim found | no interface change; no adaptation |

## Status

landed 20261021T152402-L-1922543 2026-10-21 (merge of deliver/V2/Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility)
