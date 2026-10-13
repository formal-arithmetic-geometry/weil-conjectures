# ModuleCat.projective_resolution_ext_degree

## Reason

Repair upstream review #1428 by exposing the explicit bounded-resolution/dimension
bridge for any abelian category with enough projectives. Mathlib supplies the Ext
criteria, projectivity at bound zero, and kernel dimension shifting; this theorem
constructs the bounded complex and its augmentation. Keep the existing declaration
name and node attachment. No target statement or definition changes.

## Old

```lean
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n
```

## New

```lean
theorem projective_resolution_ext_degree
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughProjectives C]
    (X : C) (n : ℕ) :
    (∃ P : ProjectiveResolution X, ∀ i : ℕ, n < i → Limits.IsZero (P.complex.X i)) ↔
      HasProjectiveDimensionLE X n
```

Specializing C to ModuleCat and unfolding HasProjectiveResolutionLE recovers
exactly the original proposition. EnoughProjectives is available for those module
universes. At n = 0 the construction uses ProjectiveResolution.self; the zero
object causes no exceptional case. The same proof generalizes to the stated
category universes. Its construction uses no data from an unproved theorem.

The source is Stacks Tag 065R (1)--(3), whose module argument is generalized
using categorical projectives and Mathlib dimension shifting. Pinned Mathlib's
unbounded resolution existence does not give the asserted support bound.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ProjectiveResolutionExtDegree | Y3 | Generalize the existing theorem; remove module-specific public imports. |
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | unclaimed | Compiles unchanged against the generalized theorem. |
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | unclaimed | Compiles unchanged against the generalized theorem. |
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | unclaimed | Forced one-line proof adaptation: remove .{u, u} (R := R) from the call. |

These are all textual declaration users and item importers in both library roots.
The first two callers keep all signatures and proofs unchanged. In the affine
caller the old call fails with Invalid argument name R and an object-universe
mismatch: ModuleCat.{u} R is Type (u + 1). Let Lean infer the category and
universes from M. The adapted file compiles; every other byte is unchanged.
Other downstream statements retain the same meaning through these unchanged
caller signatures. There are no direct public importers of this item.

Remove public imports Sheaf.RingTheory.GlobalDimension,
Mathlib.Algebra.Category.ModuleCat.Abelian, and
Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic. Public imports of projective
dimension and Projective.Resolution provide the signature's types. The projective
Ext and Augment imports are private proof dependencies. GlobalDimension remains
reachable through callers; no entire module is pruned from the target closure.

## Status

landed 20261013T222423-L-1230348 2026-10-13 (merge of deliver/Y3/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
