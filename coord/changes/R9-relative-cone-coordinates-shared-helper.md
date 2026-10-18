# AlgebraicGeometry.Etale.coneMap_XIso

## Reason

The returned delivery duplicated this existing private helper as `coneMap_coordinates`
in `RelativeCocycleCoordinates`. Relocate the original helper to that lower dependency,
expose it for reuse, and remove its old private declaration. Both relative-coordinate
naturality and short-exactness then use a single theorem with the original statement
and proof. Importing the original higher module from its own dependency would cycle.

## Old

In `Sheaf.AlgebraicGeometry.RelativeTorsorCohomology`:

```lean
private lemma coneMap_XIso
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (n : ℤ) :
    (HomologicalComplex.homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f n ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod r' n (n + 1) rfl).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod r n (n + 1) rfl).hom ≫
        biprod.map (a.f (n + 1)) (b.f n)
```

## New

In `Sheaf.AlgebraicGeometry.RelativeCocycleCoordinates`:

```lean
lemma coneMap_XIso
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) (n : ℤ) :
    (HomologicalComplex.homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h)).f n ≫
        (HomologicalComplex.homotopyCofiber.XIsoBiprod r' n (n + 1) rfl).hom =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod r n (n + 1) rfl).hom ≫
        biprod.map (a.f (n + 1)) (b.f n)
```

The old private declaration is removed. There is no `coneMap_coordinates` declaration.
The same proof is retained once, and the two coordinate proofs use `coneMap_XIso`.
No existing public statement or definition changes. No target uses this proof helper
in its statement or definitions.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.RelativeTorsorCohomology
--uses coneMap_XIso` reports no downstream modules and only the item's own three
occurrences (the declaration and two calls). The old theorem is private, hence no
external module can use it. All users of the relocated helper are delivered together.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RelativeTorsorCohomology | R9 | Remove the private helper; its two existing calls use the shared imported theorem. |
| Sheaf.AlgebraicGeometry.RelativeCocycleCoordinates | R9, new in this delivery | Replace the duplicate helper with the original theorem, public for reuse; adapt its two calls. |

The new naturality and forget-normalization modules publicly import coordinates and
compile unchanged; no forced adaptation or other holder's module is involved.

## Status

landed 20261018T092209-L-3362795 2026-10-18 (merge of deliver/R9/Sheaf.AlgebraicGeometry.RelativeTorsorCohomology)
