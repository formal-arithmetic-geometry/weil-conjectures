# integral_reductions_constructible_iff: local proof elaboration context

## Reason

The completed-coefficient, finite-coefficient and general-site tensor interfaces use
independent universes and exact scalar-restriction functors. The proof needs their
existing additivity and exactness declarations as local instances, plus concrete-universe
sheafification and site-smallness instances to resolve max-universe inference.
All changes are file-local. No existing public signature, definition body, public import
or exported instance changes, and no target-used definition changes meaning.

## Old

No additional proof-context commands beyond the pre-existing local settings.

## New

```lean
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] WeilConjectures.scalarReductionExistence
  WeilConjectures.scalarReductionDerivedExistence
attribute [local irreducible] DerivedNakayama.quotientRing
attribute [local instance] reductionSiteSmall
attribute [local instance] reductionAbSheafify reductionAbLocallyBijective reductionRingSheafify
attribute [local instance] WeilConjectures.scalarReductionExtensionAdditive
  WeilConjectures.scalarReductionRestrictionLimits
  WeilConjectures.scalarReductionRestrictionColimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits
```

The four reduction-prefixed instance proofs are new private theorems, proved from existing
library instances. Existing statements and definitions are retained verbatim.

## Users

`tools/downstream.py Sheaf.Paper.IntegralCriterionReductions --uses
integral_reductions_constructible_iff` reports eleven downstream modules and only the
item as a textual user of the theorem. Local proof commands do not propagate to importers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCriterionReductions | U4 | Resolves proof-only elaboration and exactness instances. |
| Sheaf.Paper.BrownHypothesesGeneration | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralAdicHomCompleteness | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralAdicInputNormalization | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralConstructibleExt | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralSectionLocalModels | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.Paper.IntegralStratumExtBound | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Not adapted | Same public interface and data; no consumer edit. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | Not adapted | Same public interface and data; no consumer edit. |

## Status

landed 20261024T191413-L-335524 2026-10-24 (merge of deliver/U4/Sheaf.Paper.IntegralCriterionReductions)
