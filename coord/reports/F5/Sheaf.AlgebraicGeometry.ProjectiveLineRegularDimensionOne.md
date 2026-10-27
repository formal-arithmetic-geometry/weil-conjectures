## What changed

Proved `AlgebraicGeometry.ProjectiveLine.noetherian_regular_dim_one` without changing its
signature, definitions, universes or public imports. The sole proof import is now
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth`. The already proved source
instance makes the structure morphism smooth of relative dimension one. Properness supplies
compactness; finite type supplies local Noetherianity. Smoothness supplies regular stalks,
and `IsAffineOpen.isRegularLocalRing_localization` and `isRegularRing_iff` give the required
regular affine neighbourhoods. The fixed-relative-dimension theorem gives topological
dimension one, rewritten to `Scheme.dim` by its existing equality theorem.

Updated the item's DAG proof and dependencies to this argument. The parent unit's statement
and realized proof steps remain unchanged: this is only a shorter proof of its existing
projective-line geometry prerequisite. No adopted source module was edited.

Validation: remote single-file compilation succeeded without warnings (7.9 seconds).
The axiom probes of the completed theorem and the attached source instance reported only
`propext`, `Classical.choice`, and `Quot.sound`.
The construction works for every field, including finite and imperfect fields; no
algebraic-closure or perfectness assumption is introduced. Nonemptiness comes from the
existing projective-line connected-space instance, whose proof constructs [1:1].

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProjectiveLine.noetherian_regular_dim_one`
(node `lem-sc-p1-regular-dimension-one`).

Added 0 holes; split off 0 unfinished statements. No `sorry` remains in any delivered Lean
module. The new node attaches an existing proved source instance, with no new Lean module
or declaration.

## No longer needed

Removed the private import `Sheaf.AlgebraicGeometry.IsRegularScheme`: its predicate does
not occur in this theorem's signature, which explicitly asks for regular affine
neighbourhoods. Its module is not needed by this proof; no claim is made that all other
consumers can prune it.

The following planned proof dependencies are no longer needed here:

- `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`: use properness and
  `QuasiCompact.compactSpace_of_compactSpace`.
- `lem-sc-p1-polynomial-noetherian`: use finite type over the Noetherian field spectrum.
- `lem-sc-p1-polynomial-regular`: use smoothness over the field and affine stalk localization.
- `lem-weil-pbc-localization-dimension-chains-below-prime`: use the existing smooth
  fixed-relative-dimension theorem.
- `lem-pc-ring-dimension-supremum-heights`: same reason.
- `lem-sc-p1-polynomial-dimension-one`: same reason.

These dependencies were not imported into the original item; their source declarations and
nodes are retained. The standard affine-chart construction, affine stalk-localization
identification, locally Noetherian predicate, regularity predicate and dimension definition
remain relevant and recorded in the DAG.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement needed correction. The planned polynomial-height argument was
unnecessary given the source library's completed smooth projective-line geometry and
fixed-relative-dimension theorem. The existing declaration docstring retains that valid
original argument; the updated node records the implemented shorter route.

## New nodes

`lem-sc-projective-line-smooth-relative-dimension-one` attaches the already proved
`AlgebraicGeometry.ProjectiveLine.smoothOfRelativeDimension_one` in the source module
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth`. Its statement is smoothness
of relative dimension one over any scheme. The proof uses the standard affine charts,
each with one affine coordinate. Searches of the DAG, whole blueprint and source files
found no existing node attached to this instance; LeanSearch, Loogle, LeanFinder and the
Mathlib source search found general smoothness APIs but no relative-projective-line
instance. This is a closed source-library tool, not an added hole or replacement unit
route. No change record is needed: all public interfaces are unchanged.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
