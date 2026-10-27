# Sheaf.Paper.IntegralQuotientExchangeComparison proof context

## Reason

The completed proof reuses the generic scalar/geometric exchange rectangle and its
proved section realization calculations. Local transparency attributes prevent
elaboration from expanding the large derived operations while matching their aliases.
Existing arguments and visibility are retained. The main conclusion names its
unchanged section existential as SectionExchangeRealized; its definition and the
other equivalent presentations are documented in the accompanying change records.

## Old

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The only proof of integral_quotient_exchange_comparison was sorry.

## New

The module additionally enables backward.defeqAttrib.useBackward and marks the
derived realization functors, adjunctions, comparators and mate construction locally
irreducible. ModuleRingedComparison.derivedFunctor is locally semireducible when
matching the published generic section comparison. These are elaboration commands
local to this file. No instance is added or exported.

The local attributes additionally keep ScalarComparisonRealized,
sectionScalarProjection, SectionScalarNormalized, SectionPullNormalized, rho,
scalar exchange routes and section rectangle maps folded. The attributes keep
normalization and derived mate terms folded while the abstract categorical helpers
assemble the transformations. No compile-time or heartbeat limit is raised.

The new private helpers prove natural-transformation extensionality through an
essentially surjective functor, assembly of componentwise mate-route equality as
equality of whiskered transformations, inverse-edge cancellation, and equality of
the local comparison wrappers with the generic ones. The categorical assembly
helpers use abstract category parameters; their specialization keeps the derived
localization constructions folded during kernel checking. The
scalar_comparison_realized helper proves the generator and K-flat clauses over a
general coefficient map. All private helpers are proved without sorry.

The public generic predicate ScalarComparisonRealized is documented in
D7-integral-scalar-realization-predicate.md. It is not a new assumption. Its
specialization is definitionally the original ScalarRealized.

The main proof obtains invertibility from the existing direct-image theorem by
uniqueness of normalized pull comparisons, specializes the generic internal
rectangle, chooses one normalized section family, and transports the two routes
for this same family. Essential surjectivity and cancellation give the final
natural-transformation equality with the inverse top-edge comparison last.

## Users

The downstream.py check, including --uses for all modified wrappers, found zero
downstream modules on 2026-10-25. DAG parents keep the same item node and Lean
attachment. No source-library declaration is changed, and no consumer needs an
adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralQuotientExchangeComparison | D7 | Proved private helpers and local proof context. |

## Status

landed 20261025T162207-L-354963 2026-10-25 (merge of deliver/D7/Sheaf.Paper.IntegralQuotientExchangeComparison)
