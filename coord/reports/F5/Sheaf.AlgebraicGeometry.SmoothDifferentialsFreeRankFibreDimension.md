## What changed

Proved `AlgebraicGeometry.smooth_differentials_free_rank_fibre_dimension` without changing its
signature, hypotheses, visibility or public imports. The proof chooses one standard smooth
chart with presentation dimension `d`, proves that chart has relative dimension `d`, and
uses its open pullback in the fibre to compute the dimension at `f.asFiber x`. The existing
standard-smooth Kähler equivalence supplies a basis indexed by `Fin d` on the same chart.

Proof imports now use `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` and
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmoothCotangent`. The item's DAG proof,
proof dependencies and proof origin have been updated to this route. No definitions,
statements, consumer modules or unit realizations change. No new declarations or nodes.

Validation: the item compiles cleanly through `lcompile.py`. A direct `#print axioms` of
the new proof reports exactly `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`.
The delivery dry run passed compilation, the axiom probe and preflight.
The edge cases do not require
extra assumptions: `d = 0` uses the empty basis; no nontriviality or positive-dimension
assumption is introduced, and the fibre neighbourhood contains its canonical point.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.smooth_differentials_free_rank_fibre_dimension`
(node `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-offs and no decomposition. Every mathematical theorem explicitly applied by the
new proof is already proved in Mathlib or the source library.

## No longer needed

Removed proof imports:

- `Sheaf.RingTheory.StandardSmoothDimensionAtPoints` (retired re-export).
- `WeilConjectures.RingTheory.StandardSmoothDimensionAtPoints`.

The following planned nodes are not used by this proof and were removed from its
`proof_deps`:

- `lem-weil-pbc-affine-open-spec-points`.
- `lem-weil-pbc-affine-opens-induced-ring-map-spec-square`.
- `lem-weil-pbc-spec-residue-field-identification`.
- `lem-weil-pbc-morphism-from-spec-field`.
- `lem-weil-pbc-fibre-product-affine-spectra`.
- `lem-weil-pbc-standard-smooth-base-change`.
- `lem-weil-pbc-standard-smooth-over-field-dimension-at-points`.

The explicit affine fibre-ring, Spec-point and residue-field isomorphism route is replaced
by a pullback of the open chart and the already proved smooth-over-field dimension theorem.
The general base-change theorem for relative smooth dimension also makes a separate
base-changed presentation unnecessary. The standard smooth chart and Kähler-basis nodes
remain used. This is pruning below the unit level: the item is not itself a unit statement
or realized unit step, and `dag/units/sk-thm-p1.json` stays unchanged. These removals describe
this item's proof; other library consumers may still need these nodes and modules.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically valid. It predates the proved source-library
`topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`, whose proof already supplies the
field-dimension computation. Repeating the explicit affine fibre-ring identifications is
unnecessary. The proof follows the same open-restriction pullback calculation as the proved
`Smooth.isLocallyConstant_topologicalKrullDimAt_asFiber`, using only the dimension theorem,
not a local-constancy assertion to infer a rank. Sources read: Stacks `morphisms.tex`,
`lemma-smooth-locally-standard-smooth` (01V7), `lemma-smooth-omega-finite-locally-free` (02G1),
and `algebra.tex`, `lemma-standard-smooth` (00T7), parts (2), (5), (7) and its proof.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
