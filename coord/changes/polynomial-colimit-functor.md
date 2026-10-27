# Algebra.PolynomialHomology.colimitDerived

## Reason

The concrete natural-isomorphism and normalization checks repeatedly converted
`derivedColimit bar F` to the object of a threefold composite functor. Kernel checks of
`comparison_exists` and `comparisonFamily_exists` took 12.1 and 11.5 seconds respectively.
Define the same functor with `obj F := derivedColimit bar F` and the original composite map.
The new functor is definitionally equal to the original composite: functor laws are proofs,
and the object and map formulas are unchanged. This is an implementation repair only.

## Old

```lean
/-- The universal left-derived colimit on diagrams placed in degree zero.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def colimitDerived {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v})
    (R : Type (max (u + 1) v)) [CommRing R] :
    ((Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) v} R) :=
  CochainComplex.singleFunctor _ 0 ⋙ DerivedCategory.Q ⋙
    (bar.models (Category.{u, v} f)ᵒᵖ R).derived

```

## New

```lean
/-- The degree-zero derived-colimit functor with its object formula kept explicit.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def colimitDiagram (bar : CategoryColimitBarSystem.{w}) (E : Type w) [SmallCategory E]
    (R : Type w) [CommRing R] :
    (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ DerivedCategory (ModuleCat.{w} R) where
  obj F := derivedColimit bar F
  map t := (bar.models E R).derived.map
    (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map t))
  map_id F := by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  map_comp t s := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp]
    rfl

/-- The universal left-derived colimit on diagrams placed in degree zero.
Source: Stacks 08Q9 (blueprint: lem-trf-polynomial-presentation-homology). -/
def colimitDerived {A B : CommRingCat.{u}} (f : A ⟶ B)
    (bar : CategoryColimitBarSystem.{max (u + 1) v})
    (R : Type (max (u + 1) v)) [CommRing R] :
    ((Category.{u, v} f)ᵒᵖᵒᵖ ⥤ ModuleCat.{max (u + 1) v} R) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) v} R) :=
  colimitDiagram bar (Category.{u, v} f)ᵒᵖ R

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.PolynomialPresentationHomology | V2 | Same functor, shared object formula in the comparison proofs. |
| Sheaf.RingTheory.PolynomialSquareBarNaturality | unclaimed | Downstream; does not directly use colimitDerived. Direct Mathlib import and exact alias expansion only. |
| Sheaf.RingTheory.CotangentBarTermIdentifications | unclaimed | Downstream; no direct use of colimitDerived and no adaptation required. |

The current downstream check reports the two modules above; the earlier zero-user
result is superseded. Neither uses colimitDerived directly. No target statement or mathematical
condition changes. All DAG parents and the unit route remain required. `colimitDiagram` is
attached to the existing polynomial-presentation-homology node as implementation data.

## Status

landed 20261025T005424-L-3486128 2026-10-25 (merge of deliver/V2/Sheaf.RingTheory.PolynomialPresentationHomology)
