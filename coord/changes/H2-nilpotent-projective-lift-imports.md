# CochainComplex.exists_projective_lift_of_nilpotent: remove unused public import

## Reason

The statement uses Mathlib's universal left derived functor predicate directly. It does
not need the ring-site `derivedChangeOfRings` declaration or its public reexports.
The proof computes the counit with K-projective resolutions, and the new upper-bound
adapter imports site change of rings privately. Remove the unused public import from
the item. This changes no existing declaration, definition, hypothesis, or conclusion.

## Old

```lean
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
import Sheaf.AlgebraicGeometry.ComplexLiftClassProjective
```

## New

```lean
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.ComplexLiftClassProjective
```

## Users

`tools/downstream.py Sheaf.RingTheory.NilpotentProjectiveComplexLift` listed these four
modules. The queue records each as unclaimed at the time of this check. None is edited
or adapted. The sole direct importer already imports `DerivedChangeOfRings` independently;
all statement signatures and definitions remain identical, including those used by targets.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PseudoCoherentNilpotentInvariance | unclaimed (queue) | Direct importer; imports DerivedChangeOfRings itself, so no adaptation is needed. |
| Sheaf.RingTheory.PseudoCoherentInverseRingReconstruction | unclaimed (queue) | Indirect user; the intervening module's declarations and imports are unchanged. |
| Sheaf.RingTheory.PseudoCoherentNormalizedAlgebraTower | unclaimed (queue) | Indirect user; no signature or definition changes. |
| Sheaf.RingTheory.RlimPerfectComplete | unclaimed (queue) | Indirect user; no signature or definition changes. |

## Status

landed 20261018T071156-L-1669019 2026-10-18 (merge of deliver/H2/Sheaf.RingTheory.NilpotentProjectiveComplexLift)
