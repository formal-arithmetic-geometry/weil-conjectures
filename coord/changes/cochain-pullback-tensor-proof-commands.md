# CategoryTheory.CochainPullback.cochainPullbackTensorCoherence

## Reason

The parent now contains proved private summand and coefficient-square lemmas.
The delivery classifier conservatively treats its additional universe parameters,
transparency settings and local irreducibility attributes as changes to what importers
see. The attributes are local and affect proof elaboration only. Both original public
theorem signatures and the entire HasTensorCoherence definition remain verbatim.
No target definition changes and no consumer adaptation is needed.

## Old

```lean
universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
```

## New

```lean
universe w uC vC uD vD uE vE uA vA
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] changed extensionFunctor scalarAssociation compositionModule
attribute [local irreducible] SheafOfModules.monoidalCategory
```

The two transparency settings return to true before the coefficient-square proofs.
The private generic tensor-summand lemma uses uA and vA. All new proof dependencies
are private imports; the original public imports remain verbatim.

## Users

Ran tools/downstream.py on the module, including --uses with the full
HasTensorCoherence name. The only textual user of that declaration is the item itself.
The table also includes every transitive importer the command reported. Their holders
were not queried because none is edited or requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence | Y3 | Two proofs completed; public signatures and predicate unchanged. |
| Sheaf.Algebra.Homology.RingedSiteKFlatStalkCriterion | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.AlgebraicGeometry.GeometricPointProjectionComparison | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportQuotientProduct | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.CategoryTheory.DerivedBaseChangeMap | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.Paper.EtaleProEtaleScalarMate | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.Paper.ExternalRHomConePairing | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.Paper.RingedProjectionTensorComposition | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.SixFunctors.RingedDerivedMonoidalComparisons | not queried; unchanged | No adaptation; interface unchanged. |
| Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward | not queried; unchanged | No adaptation; interface unchanged. |

## Status

landed 20261020T132056-L-1410236 2026-10-20 (merge of deliver/Y3/Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence)
