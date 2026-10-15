# Sheaf.Paper.CondensedFinitePresentationDescent proof import

## Reason

The intended sheaf-descent input cannot be imported by the TwoColimit parent while its unused
proof import of CondensedFlatCoefficientCalculus remains. That import reaches
CondensedCoefficientComparisons, which publicly imports TwoColimit, creating a cycle. The module
currently states one theorem with a sorry and uses no declaration of the calculus module in its
signature or body. Removing this one proof import breaks all paths back to TwoColimit.

CondensedFinitePresentationDescent is unclaimed. This is an adaptation permitted by the dispatcher's
2026-10-12 rule for unclaimed modules. It changes no signature, definition, visibility, proof, or
statement meaning. Its existing mathematical dependency on the flat calculus stays in its DAG node.

## Old

```lean
import Sheaf.Paper.CondensedFlatCoefficientCalculus
```

## New

The unused proof import is removed. No replacement declaration is introduced.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Remove the single unused proof import; unchanged theorem compiles. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | A2 | Import and apply exists_constructible_finiteCoefficient_model without an import cycle. |

A source search for exists_constructible_finiteCoefficient_model found no other existing declaration
users. No public imports or existing signatures change. No target statement needs re-review.

## Status

landed 20261015T172429-L-539049 2026-10-15 (merge of deliver/A2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit)
