# DerivedCategory.exists_marking_compatible_finiteFree_lift proof namespace openings

## Reason

The full proof uses mapping cones, cochain homotopies, and cokernels. Its added
`open CategoryTheory.Limits CochainComplex` command is conservatively classified as
an interface change by preflight. These namespace openings resolve names inside this
file. They declare no notation, instance, attribute, or public definition. The theorem
signature and public imports are identical. Scoping the openings to the proof term
caused two 60-second compile timeouts; the command layout below compiles in 14.3 seconds.

## Old

```lean
open CategoryTheory
namespace DerivedCategory
```

## New

```lean
open CategoryTheory
namespace DerivedCategory

open CategoryTheory.Limits CochainComplex
```

## Users

`tools/downstream.py` finds 1318 downstream modules and exactly these two textual
users of the declaration. Every existing signature and public import is unchanged,
so no consumer requires adaptation. Namespace openings are local to elaborating
this file and do not change the mathematics or the meanings of targets.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.MarkedFiniteFreeLiftCompatibility | B5 | Full proof replaces its sorry; same signature. |
| Sheaf.RingTheory.NilpotentMarkedFreeComplexLift | unclaimed | Its existing application keeps the same type and arguments. |

## Status

landed 20261020T051022-L-1531007 2026-10-20 (merge of deliver/B5/Sheaf.RingTheory.MarkedFiniteFreeLiftCompatibility)
