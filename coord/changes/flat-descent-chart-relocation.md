# AlgebraicGeometry.FlatDescentChart

## Reason

Move the chart data to its own module so that the fully proved geometric chart comparison
can import it without a cycle back through exists_flat_descent_affine_charts.
The original module publicly imports the new chart module. This is a declaration relocation:
every original definition, structure field, binder, universe, visibility and body is unchanged.
No target statement or mathematical definition changes, and no arbitrary witness is selected
in a definition. The ring diagram theorem used in the proof is fully proved.

## Old

In lean/Sheaf/AlgebraicGeometry/FlatDescentAffineCharts.lean:

```lean
/-- The ring data of one affine triple in the proof of Stacks Tag 04AI.
(blueprint: def-weil-pbc-flat-descent-chart). -/
structure FlatDescentChart (J : Type u) [Preorder J] (j₀ : J) where
  rings : J ⥤ CommRingCat.{u}
  source : CommRingCat.{u}
  target : CommRingCat.{u}
  sourceAlgebra : Algebra (rings.obj j₀) source
  targetAlgebra : Algebra (rings.obj j₀) target
  map : letI := sourceAlgebra; letI := targetAlgebra; source →ₐ[rings.obj j₀] target
  finitePresentation : map.toRingHom.FinitePresentation

namespace FlatDescentChart

/-- Flatness of the chart's tensor-product map after an arbitrary base-ring map. -/
def baseFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    {R : CommRingCat.{u}} (q : a.rings.obj j₀ ⟶ R) : Prop :=
  letI := a.sourceAlgebra
  letI := a.targetAlgebra
  letI := q.hom.toAlgebra
  (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom.Flat

/-- Flatness of a chart at a stage above its initial stage. -/
def stageFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    (j : J) (h : j₀ ≤ j) : Prop :=
  a.baseFlat (a.rings.map (homOfLE h))

/-- Flatness of the chart over the colimit of its base rings. -/
def limitFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀) : Prop :=
  a.baseFlat (colimit.ι a.rings j₀)

end FlatDescentChart
```

## New

The exact same declarations and docstrings appear in
lean/Sheaf/AlgebraicGeometry/FlatDescentChart.lean:

```lean
/-- The ring data of one affine triple in the proof of Stacks Tag 04AI.
(blueprint: def-weil-pbc-flat-descent-chart). -/
structure FlatDescentChart (J : Type u) [Preorder J] (j₀ : J) where
  rings : J ⥤ CommRingCat.{u}
  source : CommRingCat.{u}
  target : CommRingCat.{u}
  sourceAlgebra : Algebra (rings.obj j₀) source
  targetAlgebra : Algebra (rings.obj j₀) target
  map : letI := sourceAlgebra; letI := targetAlgebra; source →ₐ[rings.obj j₀] target
  finitePresentation : map.toRingHom.FinitePresentation

namespace FlatDescentChart

/-- Flatness of the chart's tensor-product map after an arbitrary base-ring map. -/
def baseFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    {R : CommRingCat.{u}} (q : a.rings.obj j₀ ⟶ R) : Prop :=
  letI := a.sourceAlgebra
  letI := a.targetAlgebra
  letI := q.hom.toAlgebra
  (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom.Flat

/-- Flatness of a chart at a stage above its initial stage. -/
def stageFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    (j : J) (h : j₀ ≤ j) : Prop :=
  a.baseFlat (a.rings.map (homOfLE h))

/-- Flatness of the chart over the colimit of its base rings. -/
def limitFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀) : Prop :=
  a.baseFlat (colimit.ι a.rings j₀)

end FlatDescentChart
```

The original module re-exports them through:

```lean
public import Sheaf.AlgebraicGeometry.FlatDescentChart
```

## Users

The downstream scan of all four original declarations finds the following textual user.
It uses stageFlat in a proof. Its original source compiles against the sandbox overlay.
All other downstream modules use the unchanged existence theorem or inferred structure
fields; public re-export preserves these too. There are no adapted existing modules.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation | unclaimed | Chart declarations are publicly re-exported with identical signatures and bodies; no edit needed. |

## Status

landed 20261013T015609-L-3025423 2026-10-13 (merge of deliver/Q4/Sheaf.AlgebraicGeometry.FlatDescentAffineCharts)
