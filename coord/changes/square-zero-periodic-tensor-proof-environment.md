# Sheaf.Paper.SquareZeroPeriodicTensor proof environment

## Reason

Stage-3 preflight requires a change record for added variable, open, notation and
attribute commands. The added commands support complete private proofs of the two
existing theorems. All helper declarations are private. Broad sheafification
instances are local. Five additional proved instances register properties of the
private lift and constant-functor constructions, and are documented below.

Each new instance head contains the private basisLift, periodicUnitLift or
periodicConstantFunctor construction. These heads cannot match an unrelated
existing object or functor. They supply isomorphism and exactness facts when the
private construction is reused in the final calculation. Their proofs are complete.

Both public theorem signatures, all existing public imports and the entire
squareZeroQuotientModule definition are verbatim unchanged. No target, definition
body or statement is changed. The original unit route and Lean attachment remain.

## Old

The original module-level universe and open commands, verbatim:

```lean
universe r u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

The five private helper instances below did not exist. The module had two proof holes.

## New

The replacement module-level universe and open commands, verbatim:

```lean
universe r u w uC vC c v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct
```

Additional universe variables, namespace-scoped variables and local notation support
independent site, coefficient and derived-category universes in private proofs.
Local instance attributes select existing monoidal and sheafification structures.
The following new private instance signatures are copied verbatim from the module:

```lean
private instance basisLift_iso : IsIso (basisLift.{r, uC, vC} J A B)

private instance periodicUnitLift_iso :
    IsIso (periodicUnitLift.{r, uC, vC} J A)

private instance periodicConstantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (periodicConstantFunctor.{r, uC, vC} J A)

private instance periodicConstantFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (periodicConstantFunctor.{r, uC, vC} J A)

private instance periodicConstantFunctor_additive :
    (periodicConstantFunctor.{r, uC, vC} J A).Additive
```

After constructing and proving the comparison API for the private constant-module
functor, the module adds the following command:

```lean
attribute [irreducible] periodicConstantFunctor
```

Later tensor calculations use the proved exactness and unit/algebra comparisons,
so they do not unfold the full sheafification composition. Its definition body is
unchanged by this attribute. The final public proof shares the canonically typed
cohomology isomorphism proof with the nonvanishing argument.

All five proofs are complete. The public statements, public imports and canonical
quotient-module definition have identical old and new text. No public data is
replaced by a private construction.

## Users

`python3 tools/downstream.py Sheaf.Paper.SquareZeroPeriodicTensor` reports zero Lean
modules downstream. The unfinished DAG parents still require the item; it is not
withdrawn. No other module is adapted by this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SquareZeroPeriodicTensor | M1 | Complete private proofs and their instance registrations; public declarations unchanged. |

## Status

landed 20261021T111314-L-71923 2026-10-21 (merge of deliver/M1/Sheaf.Paper.SquareZeroPeriodicTensor)
