# CategoryTheory.commRingSheafCompose

## Reason

Profiling the unchanged statement found about 26 seconds of repeated
GrothendieckTopology.HasSheafCompose inference. A local high-priority cache
returns the existing sheaf-composition instance, allowing the complete proof
to compile within the existing 60-second file limit. Its registration is local
to this module; the named declaration is added and is recorded for review.
No existing signature, definition, public import or target changes.

## Old

No declaration CategoryTheory.commRingSheafCompose existed.

## New

```lean
local instance (priority := 10000000) commRingSheafCompose
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by
  infer_instance
```

The proof uses the existing instance before registering this local one. This
is a proposition-valued cache, with no replacement of mathematical objects.
Private categorical helpers prove localization, normalization, projection
transport and uniqueness. Local irreducibility of roosF, roosEval, roosι and
DerivedCategory.Q prevents unwanted unfolding. Local instance registrations
and irreducibility annotations do not propagate to importing modules.
The additional elaboration options apply only while compiling this module;
the maxHeartbeats setting is scoped to the theorem, and the 60-second file
limit is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FlatRoosFunctorDescent | Z9 | Uses cache while elaborating its proof; original theorem signature unchanged. |

The downstream.py --uses commRingSheafCompose check finds no existing consumer
of this newly introduced declaration. No consumer needs adaptation. No target
meaning or definition changes, so no statement review is reopened.

## Status

landed 20261023T132600-L-2303370 2026-10-23 (merge of deliver/Z9/Sheaf.CategoryTheory.FlatRoosFunctorDescent)
