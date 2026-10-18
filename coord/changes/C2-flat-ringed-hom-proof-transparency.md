# CategoryTheory.homComplexFunctor (local proof elaboration)

## Reason

The new proof of `CategoryTheory.flat_ringed_ideal_complete_equivalence` uses the
projection and localization APIs of the existing Hom-complex functor. Marking this
functor locally irreducible prevents elaboration from expanding its chosen product
construction while checking the comparison isomorphisms. The attribute is local to
this file. The functor definition, its global reducibility, all existing public
signatures and visibility, and every target statement remain unchanged.

The stage-3 preflight classifies the added attribute command as a change to what other
modules see and requires this record. Its actual scope is proof elaboration in the
item module; no consumer adaptation is needed.

## Old

The namespace previously opened with this command, without a local attribute:

```lean
namespace CategoryTheory
```

## New

```lean
namespace CategoryTheory

-- All computations with the chosen Hom complex use its public projection API.
attribute [local irreducible] homComplexFunctor
```

## Users

`tools/downstream.py Sheaf.Paper.FlatRingedIdealCompleteEquivalence --uses
flat_ringed_ideal_complete_equivalence` reports zero downstream modules and only the
item module itself among textual declaration uses. Existing public signatures passed
the delivery tool's comparison. The whole three-module delivery compiled cleanly;
no existing definition or target meaning changes, so no target statement is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | C2 | Local elaboration attribute for the new proof; no public interface change. |

There are no adapted consumer modules or forced adaptations.

## Status

landed 20261018T133833-L-2674878 2026-10-18 (merge of deliver/C2/Sheaf.Paper.FlatRingedIdealCompleteEquivalence)
