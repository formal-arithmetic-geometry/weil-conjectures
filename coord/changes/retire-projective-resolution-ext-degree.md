# ModuleCat.projective_resolution_ext_degree

## Reason

Repair upstream review #1428's duplicate Ext criterion. Retire its old declaration and
its import interface. The Ext criterion itself is Mathlib's
CategoryTheory.hasProjectiveDimensionLT_iff. Preserve only the distinct, already proved
comparison between the explicit bounded-resolution predicate and Mathlib's dimension
predicate, under a name describing that comparison, in its own module. Its forward
implication now uses hasProjectiveDimensionLT_iff directly. Its reverse implication
constructs a bounded resolution by induction and the existing splicing construction.

The pinned Mathlib theorem hasProjectiveDimensionLT_iff quantifies over Ext classes;
it does not assert existence of a bounded ProjectiveResolution. Deleting the bridge
without retaining that construction would leave the affine polynomial caller unable
to produce its explicitly requested resolution. No target, definition, or caller
signature changes. This delivery does not claim to repair other cluster modules:
ProjectiveResolutionSuccSplice constructs an actual augmented resolution and remains
necessary here, rather than merely asserting Mathlib's dimension bound.

## Old

```lean
theorem projective_resolution_ext_degree
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n
```

In Sheaf.RingTheory.ProjectiveResolutionExtDegree.

## New

```lean
theorem hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE
    {R : Type u} [CommRing R] (X : ModuleCat.{max u v} R) (n : ℕ) :
    HasProjectiveResolutionLE X n ↔ HasProjectiveDimensionLE X n
```

In Sheaf.RingTheory.BoundedProjectiveResolutionDimension. The old module is an empty
retirement notice, with only a private Mathlib.Init import for command and linter support, and no declarations. It stays as a source file so that
compiling originals against its changed interface establishes the forced adaptations.
The old name is removed, with no deprecated alias and no replacement Ext criterion.
The existing node is reattached to the renamed bridge; no new mathematical node is needed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | unclaimed | Change the proof import and two bridge calls only. Signature and visibility unchanged. |
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | unclaimed | Change the proof import and two bridge calls only. Signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | unclaimed | Change the proof import and one bridge call only. Signature and visibility unchanged. |

These are all three direct importers and all declaration users reported by
`tools/downstream.py --direct --uses projective_resolution_ext_degree` and source search.
There are 429 transitive downstream modules; the other 426 have no textual use of the
retired declaration and retain the same caller interfaces. No publicly imported module
or definition used in a target statement is changed. The empty retired module provides
no declarations; every original direct caller therefore fails with Unknown identifier
at its old bridge calls against the changed interface. The delivery wrapper records
the exact counterfactual diagnostics in the report.

## Status

landed 20261014T045606-L-1571544 2026-10-14 (merge of deliver/B4/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
