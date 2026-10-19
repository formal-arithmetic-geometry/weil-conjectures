## What changed

Proved `AlgebraicGeometry.Scheme.Hom.finiteType_fibre_image_dimension_bounds` with its
original signature. The image bound uses a finite generic-point cover of the Noetherian
source, the existing proved image-point closure inequality, and dimension comparison for
a closed subset covered by closures of points. The source bound uses the existing proved
`Scheme.Hom.topologicalKrullDim_le_add`, after transferring the fibre hypothesis through
`f.fiberHomeo`. Both arguments include empty schemes.

Added proof-only imports of `WeilConjectures.AlgebraicGeometry.ClosurePointDimension`,
`WeilConjectures.AlgebraicGeometry.FiberDimension`, and
`WeilConjectures.Topology.KrullDimension.Specialization`. Kept the original public imports
and the proof import of `Mathlib.AlgebraicGeometry.Noetherian`. Updated the proof docstring
and the existing node's proof, proof dependencies, and proof origin to match this route.
Two new DAG records attach existing fully proved source declarations; no Lean module or
statement is added for them. No definition, public signature, or target statement changes.

Single-file compilation succeeded. `#print axioms` for the completed declaration reports
exactly `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.
The final signature was compared with the original using the project's declaration reader
and is identical. All Lean lines are at most 100 characters.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Hom.finiteType_fibre_image_dimension_bounds`
(node `lem-zl-finite-type-fibre-image-dimension-bounds`).

Holes remaining in the assigned module: 0. Holes added: 0. Statements split off: 0.
The two new nodes record existing proved source theorems, so they add no proof obligation.
This is a completed proof, not a decomposition into lower holes.

## No longer needed

Removed these direct proof imports:

- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `Sheaf.DeligneLaumon.IrreducibleFibreDimensionLowerBound`

Removed these planned direct node dependencies:

- `def-kun-topological-dimension-at-point`: no local-dimension minimum is needed.
- `lem-kun-dimension-finite-type`: neither bound needs finite global dimensions.
- `lem-pc-closed-imm-base-change`: no component fibre is constructed.
- `lem-sfb-finite-type-composition-base-change`: no component closed subschemes or base changes
  are used in the new proof.
- `lem-weil-pbc-closed-immersion-finite`: no closed immersion is constructed.
- `lem-weil-pbc-closed-subset-closed-subscheme`: generic points suffice for the image cover.
- `lem-weil-pbc-immersion-base-change-lft`: no component immersion is constructed.
- `lem-zl-irreducible-fibre-dimension-lower-bound`: the two existing proved inequalities
  replace the entire dimension-difference/dense-open-equality argument.

These are removals from this item's direct proof route. Some Mathlib or source modules
remain transitive imports of the retained proved tools; this report does not assert that
all the listed modules disappear from the whole targets' import closure.
The unit's realized statement and proof-step lists are empty, so no required unit
realization is bypassed. No node or module is withdrawn or deleted.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and the proposed componentwise proof are sound, but the DAG
missed existing proved source-library results that give a substantially shorter proof.
The module named for `lem-pc-closed-imm-base-change` is `Modules.VeryAmple`, whose recorded
`IsVeryAmple.pullback_of_field` declaration is not the general closed-immersion base-change
statement needed by the old plan. That dependency is pruned, so no repair is needed here.

## New nodes

`lem-zl-image-point-closure-dimension-bound` attaches the existing proved
`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_closure_singleton_apply_le` in
`WeilConjectures.AlgebraicGeometry.ClosurePointDimension`. It compares dimensions of
closures of a point and its image for locally finite type morphisms over a field.
The record gives the unchanged source signature, complete proof in words, and three
kinds of search. It introduces no Lean declaration or sorry.

`lem-zl-source-dimension-fibre-bound` attaches the existing proved
`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_add` in
`WeilConjectures.AlgebraicGeometry.FiberDimension`. It bounds source dimension by target
dimension plus a uniform topological-fibre bound over a locally Noetherian target.
The record gives the unchanged source signature, complete proof in words, and three
kinds of search. It introduces no Lean declaration or sorry.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
