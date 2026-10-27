# Sheaf.Paper.QcqsProperConstructibleClosedBaseChange proof context

## Reason

The bounded constructible closed-exchange proof uses an abstract finite-Postnikov lemma
and the existing private isomorphism-closure theorem imported using `import all` from
`Sheaf.Paper.IndConstructibleFilteredColimits`. The abstract lemma has independent
category universes. Shift
notation needs the existing Obj scope. Local irreducibility annotations stop elaboration
from expanding coefficient inverse images and canonical derived shift structures.
These commands are the only static interface differences flagged by preflight; the
coefficient definition and the public theorem signature remain verbatim. All the
attributes are explicitly local and no definition body or instance value changes.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits
```

There were no local irreducibility annotations in this module.

## New

```lean
universe u uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
```

In the proof section in namespace AlgebraicGeometry.ProEtale.CondensedRing:

```lean
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar lowerStar upperStarFromPoint condensedAmbientExchange
  modulePullbackDerivedCommShift modulePushforwardDerivedCommShift modulePullbackExactComparison
```

The private proved Postnikov helper consumes these commands. The public theorem still has
exactly its original universe u; the additional universes occur only in its private
abstract induction helper. The original public imports are preserved exactly.

## Users

Read-only tools/downstream.py lists one downstream module. No consumer needs an edit:
none of these local attributes or lexical scopes is exported, and the theorem and
coefficient predicate retain their signatures and bodies respectively.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | N1 | Private proof context and proved helpers; public theorem signature and coefficient definition unchanged. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | not adapted | No statement, import visibility, or proof-interface change. |
| Sheaf.Paper.ProperConstructibleClosedExchangeHeart | N1, new | New degree-zero subargument with its own DAG node and one named sorry. |

No target statement or mathematical definition changes. No forced adaptation is needed.

## Status

landed 20261024T015231-L-2343414 2026-10-24 (merge of deliver/N1/Sheaf.Paper.QcqsProperConstructibleClosedBaseChange)
