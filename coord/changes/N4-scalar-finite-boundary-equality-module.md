# Scalar finite-boundary theorem modules

## Reason

Keep both original theorem signatures and all mathematical definitions unchanged
while meeting the 60-second limit. After replacing concrete derived-functor
rewrites with proved generic transport laws, the combined proof checked without
holes in 81.2 seconds: 54.3 seconds checking the boundary theorem and 16.7 seconds
checking the composition theorem. Extracting only the witness theorem still took
62.6 seconds. The direct square calculation and witness packaging are therefore
compiled separately, with the actual equation proved first. No limit is raised.

## Old

The following two public declarations were in
`Sheaf.Paper.ScalarFiniteBoundaryComposition`:

```lean
theorem scalarFiniteBoundary_composition (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        scalarFiniteBoundary_eval l E c f n =
      scalarFiniteBoundary_integral l E c f n ≫
        (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (finiteRootMap l E T n)⟦(2 : ℤ)⟧'
```

```lean
theorem scalarFiniteBoundary_boundaryEquality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hc : unitNormalization c.scalar.T
      (SemilinearSections.res.{u + 1, u, u + 1} (coefficientSystemMap l E T))
      c.scalar.adjunction c.scalarUnit (scalarGenerator l E T))
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n)⟦(2 : ℤ)⟧')
      (scalarFiniteBoundary_eval l E c f n)
      (scalarFiniteBoundary_integral l E c f n)
```

## New

The exact same composition signature lives in
`Sheaf.Paper.ScalarFiniteBoundarySquare`, with a complete direct proof from the
proved scalar transpose, endpoint identifications and generic exact transport.
The exact same boundary-equality signature lives in
`Sheaf.Paper.ScalarFiniteBoundaryEquality`; its complete proof packages the
composition equation with reflexive HEq witnesses.

The item publicly imports `ScalarFiniteBoundaryEquality`, which publicly imports
`ScalarFiniteBoundarySquare`, which publicly imports `ScalarFiniteBoundaryArrows`.
Every existing name and original public dependency remains available to importers.
Only the unused private proof helper `finiteBoundaryEquality_comp` is removed.
The two original DAG nodes retain their statements and now record these module
attachments and the actual proof direction (equation first, witnesses second).
There are no added proof holes and no changed target interpretations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarFiniteBoundaryComposition | N4 | Publicly reexports both original theorems and both original definitions. |
| Sheaf.Paper.TowerScalarFiniteBoundary | unclaimed | Its original source is compiled unchanged against this delivery. |

## Status

landed 20261028T055728-L-801789 2026-10-28 (merge of deliver/N4/Sheaf.Paper.ScalarFiniteBoundaryComposition)
