# AlgebraicGeometry.ProEtale.CondensedRing.properLowerStar_constructible_cohomology_ellAdic

## Reason

Delivery preflight requested a change record for added commands (`open` and local
`irreducible` attributes). These are proof elaboration controls in the item module;
they prevent repeated unfolding of derived functor choices and monoid structures.
All attributes are explicitly local. The theorem signature, visibility and attributes
are unchanged, as are the four public imports. Added proof imports are private.
No definition, instance or statement has changed. No consumer requires adaptation.
The repaired complete module compiled cleanly through lcompile.py in 25.8 seconds.
The two duplicate private helpers flagged by the return at `c7581c10e` are removed;
private `import all` accesses the existing lemmas in FiniteProperClassicalCoproducts
and LocalizingClosureCtfEqualsBc instead. These imports introduce no cycle.

## Old

The command block before the original theorem was:

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
```

## New

The command block before the proved private helpers is:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj
  Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived
```

The existing public theorem has precisely the same signature. Its sole sorry is
replaced by a proof using the private helpers. This record documents a conservative
static-check trigger, not a changed mathematical interface.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology
--uses properLowerStar_constructible_cohomology_ellAdic` lists these downstream
modules. Only the source ProperLowerStarEllAdic module directly mentions the theorem;
its original call is unchanged and still has the same type. No downstream module is
included or edited in this packet.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed at check | unchanged interface; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts` | unclaimed at check | unchanged interface; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed at check | unchanged interface; no adaptation |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | unclaimed at check | unchanged interface; no adaptation |
| `Sheaf.Paper.NativeAdicCompactSupportSums` | unclaimed at check | unchanged interface; no adaptation |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | unclaimed at check | unchanged interface; no adaptation |
| `WeilConjectures` | unclaimed at check | unchanged interface; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | unclaimed at check | unchanged interface; no adaptation |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing` | unclaimed at check | unchanged interface; no adaptation |

## Status

landed 20261024T015202-L-2337610 2026-10-24 (merge of deliver/M2/Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology)
