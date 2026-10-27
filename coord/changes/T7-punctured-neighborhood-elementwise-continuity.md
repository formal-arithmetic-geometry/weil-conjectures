# TopCat.puncturedNeighborhoodCohomology_colimit

## Reason

The canonical comparison can be proved invertible by the two independent elementwise
parts of continuity: lifting target classes and killing zero-image classes after shrinking.
The proof combines these using the filtered colimit of abelian groups. The new statements
name these parts without asserting the parent's isomorphism conclusion.

## Old

The assigned theorem has the following unchanged signature and had a `sorry` proof:

```lean
theorem puncturedNeighborhoodCohomology_colimit
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ) :
    IsFiltered (compactOpenNeighborhoods Z)ᵒᵖ ∧
      IsIso (colimit.desc (puncturedNeighborhoodCohomologyDiagram Z hZ A p)
        (puncturedNeighborhoodCohomologyCocone Z hZ A p))
```

The two new modules and their declarations did not exist.

## New

The assigned signature is unchanged. Its proof is the filteredness, injectivity and
surjectivity argument. New private imports provide Mathlib's element representation and
the following two public statements, each in its own new module:

```lean
theorem puncturedNeighborhood_cohomology_class_lift
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (y : (puncturedNeighborhoodCohomologyCocone Z hZ A q).pt) :
    ∃ (N : (compactOpenNeighborhoods Z)ᵒᵖ)
      (x : (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj N),
      ((puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app N).hom x = y

theorem puncturedNeighborhood_cohomology_eventual_zero
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (N : (compactOpenNeighborhoods Z)ᵒᵖ)
    (x : (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj N)
    (hx : ((puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app N).hom x = 0) :
    ∃ (M : (compactOpenNeighborhoods Z)ᵒᵖ) (f : N ⟶ M),
      ((puncturedNeighborhoodCohomologyDiagram Z hZ A q).map f).hom x = 0
```

Both are named unfinished theorems with source, complete proof in words and matching DAG
nodes. No data is chosen from either theorem in a definition. Their witnesses are
eliminated only in the proposition proof of the assigned theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit | T7 | Complete proof; private imports of the two new statements. |

No existing statement, definition, instance or public import is changed, and no other
module needs adaptation. Each new statement's only current consumer is the assigned module.

## Status

landed 20261024T020608-L-2624606 2026-10-24 (merge of deliver/T7/Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit)
