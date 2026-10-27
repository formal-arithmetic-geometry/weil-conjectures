# AlgebraicGeometry.ProEtale.reductionCompatibilities_purity

## Reason

The proof reuses already proved ordinary scalar tensor and finite-origin helpers.
Its private helpers are placed in the ordinary finite-purity namespace for direct
access to those constructions. The source-interface detector conservatively records
the new namespace/open commands and the one-declaration local instance adjustment.
No existing public signature, definition body, attribute, instance, or import changes.

## Old

The item had its existing AlgebraicGeometry.ProEtale namespace and settings, with
no separate private-helper namespace. All three public theorem signatures and the
existing public imports were exactly those retained by this delivery. The old scope
boundary, verbatim, was:

```lean
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
```

## New

Before the existing namespace, add a closed
`namespace AlgebraicGeometry.Etale.FiniteSmoothPurity` with `open MonoidalCategory`
and five proved private helper theorems. The ordinaryGammaCoefficient helper uses
`attribute [-instance] CategoryTheory.catToReflQuiver in`, confined to that declaration,
to select the existing derived-category Hom instance consistently. Both namespace
and local instance scope end before the original declarations. Add only private
proof imports of ExceptionalCoefficientComparison, FiniteSmoothLevelOfOrientation,
and ReductionOrientation. The original theorem signatures and all public imports
are verbatim unchanged. No target definition or mathematical meaning changes. The
new closed scope has the following command boundaries (the enclosed declarations
are the five proved private theorems in the module):

```lean
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
open MonoidalCategory
```

The declaration-local adjustment is exactly:

```lean
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinaryGammaCoefficient
```

After the helpers the scope ends with:

```lean
end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale
```

## Users

The source census has three transitive importers, listed below. None needs adaptation;
all new helpers are private and the instance adjustment is declaration-local.
The new ReductionOrientation module is a proof dependency, not a changed existing
interface; its only consumer in this delivery is the item itself.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteDncNormalizationReduction | Unclaimed | Existing interface unchanged. |
| Sheaf.Paper.FiniteOrientationReduction | W9 | Existing interface unchanged. |
| Sheaf.Paper.PurityConjugatesTowerReduction | B3 | Existing interface unchanged. |

## Status

landed 20261025T181322-L-4152524 2026-10-25 (merge of deliver/X6/Sheaf.SecSmoothPurity.ReductionCompatibilities)
