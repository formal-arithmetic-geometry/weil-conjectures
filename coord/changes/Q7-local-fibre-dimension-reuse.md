# AlgebraicGeometry.exists_bounded_fibre_dimension_neighbourhood

## Reason

Repair the duplicate-proof return of Q7's LocalFibreDimensionOpen delivery. The existing
neighbourhood theorem already proves exactly the local geometric input needed for
openness. It is private, so expose that theorem in its original, unclaimed module
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound` and reuse it. Its proof and type
are unchanged. The other three private comparison helpers remain in that module only.

The exposed statement uses `topologicalKrullDimAt`, so it additionally requires
`public import WeilConjectures.Mathlib.Topology.KrullDimension`. This adds visibility;
it changes no definition, existing public statement, or target meaning.

## Old

```lean
private theorem exists_bounded_fibre_dimension_neighbourhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (d : ℕ) (hd : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ W : X.Opens, x ∈ W ∧
      ∀ z ∈ W, topologicalKrullDimAt (f.asFiber z) ≤ (d : WithBot ℕ∞)
```

The local dimension module was available only through private proof imports.

## New

```lean
theorem exists_bounded_fibre_dimension_neighbourhood
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (d : ℕ) (hd : topologicalKrullDimAt (f.asFiber x) = (d : WithBot ℕ∞)) :
    ∃ W : X.Opens, x ∈ W ∧
      ∀ z ∈ W, topologicalKrullDimAt (f.asFiber z) ≤ (d : WithBot ℕ∞)
```

Add `public import WeilConjectures.Mathlib.Topology.KrullDimension` to make the type
of the exposed theorem available to importers. Add a source/proof docstring and a DAG
attachment for this existing theorem. There is no new theorem proof or hole.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound --uses
AlgebraicGeometry.exists_bounded_fibre_dimension_neighbourhood` found only its defining
module: it had no external users while private. The new user and all four direct
importers are listed below. All existing public statements stay identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound | unclaimed | Expose existing helper; proof unchanged. |
| Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen | Q7 | Import and use helper; remove four duplicate private proofs. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Additive visibility only; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | Additive visibility only; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | unclaimed | Additive visibility only; no adaptation needed. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Additive visibility only; no adaptation needed. |

The changed module and its new user compile. Unchanged direct importers
`EllAdicProperTruncationBound`, `ProperDerivedDirectImageCoproducts` and
`LowerShriekFunctoriality` compile against the sandbox. The unchanged `UpperShriek`
check stops on its unrelated unpublished import object
`Sheaf.CategoryTheory.RightDerivedFunctorUpperBound`; it needs no source adaptation.

## Status

landed 20261018T071215-L-1675333 2026-10-18 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen)
