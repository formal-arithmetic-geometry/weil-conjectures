# TopCat.Sheaf.spectralLimitCohomologyMap

## Reason

Relocate the existing canonical map to an independent module so the three proof subarguments can state their conclusions without importing the theorem that uses them. This avoids an import cycle. The main module publicly imports the helper, preserving the declaration's availability to every current importer.

## Old

In `Sheaf.Topology.SpectralLimitCohomology`:

```lean
noncomputable def spectralLimitCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    {F : Y.Sheaf AddCommGrpCat.{u}} {G : X.Sheaf AddCommGrpCat.{u}}
    (α : F ⟶ (pushforward AddCommGrpCat.{u} f).obj G) (q : ℕ) :
    CategoryTheory.Sheaf.H' F q ⊤ ⟶ CategoryTheory.Sheaf.H' G q ⊤ :=
  c q ⊤ F ≫
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q).map
      ((sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).homEquiv F G |>.symm α))).app
      (op ((Opens.map f).obj ⊤)) ≫
    (CategoryTheory.Sheaf.cohomologyPresheaf G q).map
      (eqToHom (congrArg op (Opens.map_top f)))
```

## New

In `Sheaf.Topology.SpectralLimitCohomologyMap`, publicly imported by the old module:

```lean
noncomputable def spectralLimitCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    {F : Y.Sheaf AddCommGrpCat.{u}} {G : X.Sheaf AddCommGrpCat.{u}}
    (α : F ⟶ (pushforward AddCommGrpCat.{u} f).obj G) (q : ℕ) :
    CategoryTheory.Sheaf.H' F q ⊤ ⟶ CategoryTheory.Sheaf.H' G q ⊤ :=
  c q ⊤ F ≫
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q).map
      ((sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).homEquiv F G |>.symm α))).app
      (op ((Opens.map f).obj ⊤)) ≫
    (CategoryTheory.Sheaf.cohomologyPresheaf G q).map
      (eqToHom (congrArg op (Opens.map_top f)))
```

The name, universes, binders, result type, reducibility and expression are identical. No target meaning changes. The parent node's Lean attachment now contains only its theorem; a new definition node records the moved definition.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.SpectralLimitCohomology | V3 | Publicly re-exports the moved definition; theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.TopCoherentCohomologyFinite | R1 | Imports the original module; no signature or proof adaptation required. |
| Sheaf.AlgebraicGeometry.TopDegreeOpenRestrictionSurjective | S2 | Imports the original module; no signature or proof adaptation required. |
| Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit | U2 | Imports the original module; no signature or proof adaptation required. |

`tools/downstream.py Sheaf.Topology.SpectralLimitCohomology --uses spectralLimitCohomologyMap` lists these three downstream modules and finds textual uses only in the item itself. Original consumer sources are checked against the delivered overlay. No consumer is edited or included in the delivery.

## Status

landed 20261018T071236-L-1681912 2026-10-18 (merge of deliver/V3/Sheaf.Topology.SpectralLimitCohomology)
