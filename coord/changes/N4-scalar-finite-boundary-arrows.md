# scalarFiniteBoundary_eval and scalarFiniteBoundary_integral

## Reason

Extract the two existing definitions verbatim into the new module
`Sheaf.Paper.ScalarFiniteBoundaryArrows`, reexported publicly by the item.
Their elaborated endpoint types are expensive to check repeatedly. Profiling the
original layout found kernel checking of these inferred types to be the main
cost; the original item took about 79 seconds before its hole was filled.
With the unchanged definitions compiled once in their own module, that module
took 27.3 seconds and the original item with its existing proof skeleton took
28.9 seconds. No mathematical definition, signature, binder, attribute or target
statement changes. The completed proof is checked separately below.

## Old

In `Sheaf.Paper.ScalarFiniteBoundaryComposition`, publicly importing
`Sheaf.Paper.TowerScalarFiniteBoundaryData`:

```lean
def scalarFiniteBoundary_eval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  forgetEvaluatedArrow (SpTowerShriek.ev l E T n) (finiteForget l E T n)
    (lineEvaluation l E c n) (scalarChernArrow l E c f)

/-- The integral evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_integral (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  mapSingleArrow (abEvaluation T n) (2 : ℤ) (underlyingChernArrow l c f)
```

## New

The same declarations now live in `Sheaf.Paper.ScalarFiniteBoundaryArrows`, which
publicly imports `Sheaf.Paper.TowerScalarFiniteBoundaryData`:

```lean
def scalarFiniteBoundary_eval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  forgetEvaluatedArrow (SpTowerShriek.ev l E T n) (finiteForget l E T n)
    (lineEvaluation l E c n) (scalarChernArrow l E c f)

/-- The integral evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_integral (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  mapSingleArrow (abEvaluation T n) (2 : ℤ) (underlyingChernArrow l c f)
```

The item replaces its public import with:

```lean
public import Sheaf.Paper.ScalarFiniteBoundaryEquality
```

This publicly reexports `ScalarFiniteBoundarySquare`, which publicly imports
`ScalarFiniteBoundaryArrows`. The companion change record documents the two
existing theorem moves.

The original two theorem signatures are unchanged. Their nodes now cite the new
arrow-definition node as a statement dependency, and the composition node's Lean
attachment no longer lists definitions living in a different module.
The definitions retain exactly the same meaning, so this extraction does not
reopen the mathematical interpretation of any target.

## Users

`tools/downstream.py --uses` reports only the item itself as a textual user of
each moved name. There is one direct importer of the item. Other transitive
importers retain the same public definitions through the new public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarFiniteBoundaryComposition | N4 | Imports and reexports the new module; theorem signatures unchanged. |
| Sheaf.Paper.TowerScalarFiniteBoundary | unclaimed | Original source is compiled unchanged against this delivery. |

## Status

landed 20261028T055728-L-801789 2026-10-28 (merge of deliver/N4/Sheaf.Paper.ScalarFiniteBoundaryComposition)
