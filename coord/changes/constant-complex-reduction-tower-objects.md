# AlgebraicGeometry.ConstantComplexBaseChange.ReductionData.tower

## Reason

The unclaimed quotient-model module's tower is an opaque wrapper around a sequence
functor and flip. Profiling the actual Roos construction showed 20–28 seconds in
kernel checking its carrier conversions; the full file repeatedly exceeded the
60-second limit. Expose the tower's object function as a reducible wrapper, retaining
exactly the original sequence maps, identity laws and composition laws. This makes
the finite coefficient complex visible without expanding its implementation.
The resulting tower is definitionally equal to the original one; no object, map,
normalization condition or differential changes.

## Old

```lean
def ReductionData.tower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) :=
  (Functor.ofOpSequence (X := fun n ↦ finiteOverCompleted W I n) e.step).flip
```

## New

```lean
abbrev ReductionData.tower (W : Scheme.{u}) {R : Type u} [CommRing R] (I : Ideal R)
    {d : FiniteTower W I} (e : ReductionData W I d) :=
  let F : ℕᵒᵖ ⥤ (ScalarComplex R ⥤
      CochainComplex (proEtaleRingModules W (completed W I)) ℤ) :=
    { obj := fun n ↦ finiteOverCompleted W I n.unop
      map := (Functor.ofOpSequence e.step).map
      map_id := (Functor.ofOpSequence e.step).map_id
      map_comp := (Functor.ofOpSequence e.step).map_comp }
  F.flip
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantComplexQuotientModel | unclaimed | Same tower objects and maps, exposed by a reducible wrapper. |
| Sheaf.Paper.ConstantComplexStrictBaseChange | K2 | Roos carrier conversions use the finite complex directly. |
| Sheaf.Paper.ConstantComplexStrictBaseChangeData | K2, new | Unchanged comparison interfaces use the same tower. |
| Sheaf.Paper.ConstantComplexNormalizedReductions | K2, new | Same quotient-model normalization proposition. |
| Sheaf.Paper.ConstantComplexFinitePullback | K2, new | Does not use the reduction tower. |
| Sheaf.Paper.ConstantComplexCompletedPullback | K2, new | Same quotient-model interfaces. |

`tools/downstream.py` lists the original item as the only downstream Lean module.
All existing consumers are included. No theorem of Challenge.lean changes. The
underlying tower remains definitionally identical and the normalization predicate
is unchanged.

## Status

landed 20261025T163806-L-839447 2026-10-25 (merge of deliver/K2/Sheaf.Paper.ConstantComplexStrictBaseChange)
