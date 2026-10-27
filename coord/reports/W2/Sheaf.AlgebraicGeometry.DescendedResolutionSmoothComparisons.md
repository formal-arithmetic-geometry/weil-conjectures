## What changed

Replaced the hole in `Sheaf.AlgebraicGeometry.DescendedResolutionSmoothComparisons` by a
constructor proof using one smooth comparison for each morphism. Added
`Sheaf.AlgebraicGeometry.OrdinaryResolutionLevelMapRigidity`, which proves uniqueness
of the maps into all tower levels from the existing blowup universal property.
Added `Sheaf.AlgebraicGeometry.AffineCoverOrdinaryResolutionComparison` for the remaining
single-map gluing step. All existing declaration signatures, definitions and public
imports are unchanged. Only this item, the two new modules and their DAG nodes change.

The assembly proves identity/composition of ordered survivor embeddings using label
injectivity; it proves count composition by induction, including each deletion case.
The level-map equations and canonical flat blowup normalization follow from the proved
rigidity theorem. The local deletion criterion is proved by pulling support points
through the source affine cover. Surjective nondeletion follows from base change of
surjectivity and nonempty center supports. An empty regular tower has length zero
because any first center point would map to the empty base.

Rigidity is proved by three inductions: invertible ideals remain invertible under
later blowups, centers become invertible at their own blowup and remain so, and lifts
into each earlier level are unique by the blowup universal property. It does not
assume reducedness or dense-open extension in its proof.

Validation: the item compiles in 5.2 seconds; the rigidity module compiles in 4.0 seconds.
The single-map module also compiles. All Lean lines are within 100 columns.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.OrdinaryResolutionDescent.descendedResolution_smoothComparisons`
(node `lem-trf-descended-resolution-smooth-comparisons`). This is a decomposition,
with a complete Lean assembly proof and one smaller remaining theorem, rather than
an unconditional sorry-free resolution-descent theorem.

New proved theorem:
`AlgebraicGeometry.OrdinaryResolutionDescent.smoothComparison_levelMap_unique`
(node `lem-trf-ordinary-resolution-level-map-rigidity`). Its private helpers are all proved.

One hole added, and the only hole left in the delivered modules:
`AlgebraicGeometry.OrdinaryResolutionDescent.affineCover_ordinaryResolution_comparison`
(node `lem-trf-affine-cover-ordinary-resolution-comparison`). It constructs a comparison
for a single smooth morphism with all cover restrictions. It contains no global rule,
identity/composition, canonical-step or empty-input conclusions. Its complete gluing
argument and sources are in its docstring and node. Original holes closed: 1. Holes
added: 1. Item module holes remaining: 0. Delivery total holes remaining: 1.

## No longer needed

Removed proof imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber` and
`Mathlib.AlgebraicGeometry.Gluing` from the item. Smooth flatness uses the standard
instance; cover gluing is isolated in the remaining comparison theorem. Kept
`Mathlib.AlgebraicGeometry.PullbackCarrier` for pullback points and surjectivity.

The affine tensor-chart calculation and the dependency
`lem-sfb-flat-pullback-blowup-chart-restrictions`, module
`Sheaf.AlgebraicGeometry.FlatPullbackBlowupChartRestrictions`, are unnecessary for
this proof route, including the remaining gluing step: uniqueness of blowup lifts
identifies maps over their base. Removed its old top-level `tool_uses` approval
from the item node. The canonical-step result is still exactly the published flat
blowup comparison, proved using its structural-map equation and rigidity.

Other old dependencies remain in the logical closure through the one-map descent
node or the proved rigidity node. No existing module is withdrawn. No source-library
declaration or proof is removed or replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

The old plan can be shortened below the unit level: chart fraction calculations are
not required for level-map coherence. The existing proved universal-property API
provides uniqueness, after propagating invertible center ideals along the tower.
The retained embedding laws follow directly from injectivity of the fixed labels;
the count laws follow by finite induction, avoiding an additional ideal-extension
argument for composition. The empty-input clause follows already from nonempty
centers. The target statement and the unit route are unchanged.

The new single-map gluing theorem is strictly smaller than the assigned theorem.
It omits the global rule and every identity/composition, canonical-step,
surjectivity and empty-input result; the item proves those conclusions explicitly.

## New nodes

`lem-trf-ordinary-resolution-level-map-rigidity` attaches the new proved theorem in
`OrdinaryResolutionLevelMapRigidity.lean`. Its proof uses the existing principalization,
Cartier total-transform, flat Cartier pullback and blowup universal-property results.
These are generic tools, not a replacement of a unit route.

`lem-trf-affine-cover-ordinary-resolution-comparison` attaches the remaining named
hole in `AffineCoverOrdinaryResolutionComparison.lean`. It isolates original steps
1--6: subordinate finite covers, synchronized indices, local level-map gluing and
cover independence. Its proof uses the new proved rigidity result instead of the
old unresolved tensor-chart theorem. No change record is required: no existing
statement, definition or public interface changes.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
