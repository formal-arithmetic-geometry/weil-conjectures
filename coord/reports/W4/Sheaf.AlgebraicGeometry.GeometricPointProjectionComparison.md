## What changed

Proved `AlgebraicGeometry.Etale.geometricPoint_projection_comparison` from the existing
categorical theorem `Adjunction.rightAdjointProjectionMap_mate`, the specified derived
sections counit equation, and one separate pullback/stalk tensor-normalization statement.
All existing public signatures and definitions are unchanged. The proof-only import
`Sheaf.Paper.RingedProjectionTensorComposition` is replaced by
`WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat` and the new normalization
module. The original node's proof and dependencies now describe this route.

The proof contains three proved private categorical helpers. `projection_square` applies
the mate theorem and uses projection naturality to remove the coefficient germ unit.
`transport_counit` transports the recorded counit identity through the exact-functor
isomorphisms. `pullbackStalk_unit` derives the required coefficient equation from
naturality and the left triangle identity. No compatibility of projection maps is assumed.

The new module constructs the evaluation comparison explicitly as inverse to the canonical
constants comparison followed by inverse image of the point-equivalence counit. Its transparent
`PullbackStalkTensorCompatible` formula keeps elaboration from expanding the derived tensor
localization objects. This matters: specializing a fully expanded categorical hypothesis
exceeded the per-file compile limit; naming the formula makes the same proof compile cleanly
without changing definitions, splitting the item file, or raising the limit.

Validation: both modules compiled with `lcompile.py`; the final delivery dry run also checks
the packet, import direction and consumers. The normalization theorem was checked on the
identity morphism, zero input objects, the empty scheme Z, and unbounded complexes. Both
ordinary routes send a tensor of germs to the tensor of their evaluated pulled-back sections;
the signed total-complex construction uses identical degree-zero maps and signs. No torsion,
boundedness, properness, or nonemptiness hypothesis is used.

## Proved and sorry left

Original module: one hole, in
`AlgebraicGeometry.Etale.geometricPoint_projection_comparison`; that declaration now has a
complete compiling proof. There are zero `sorry` occurrences in the item module.

Added: one hole, in
`AlgebraicGeometry.Etale.geometricPoint_pullbackStalk_tensor`, node
`lem-kun-geometric-point-pullback-tensor-normalization`, in the new module
`Sheaf.AlgebraicGeometry.GeometricPointPullbackTensorNormalization`.
Its proof is exactly `by sorry`, with its source and complete proof in words in its docstring
and node. No definition or private helper contains a hole.

This is a decomposition: one original hole closed and one strictly separate tensor-only hole
added, so the delivery claims no net hole reduction. The tensor lemma has no derived direct image or projection map. The real Lean argument combines it with the counit
comparison, the projection-mate theorem, naturality and the triangle identity. Existing
imported theorem holes are not new holes in this delivery.

## No longer needed

Removed proof import `Sheaf.Paper.RingedProjectionTensorComposition`, and removed
`lem-sfb-ringed-projection-tensor-composition` from the item's `proof_deps` and `tool_uses`.
The item does not need its ringed-corner models, arbitrary ringed-topos composition and
section packages, tensor associativity/symmetry assertions, or any conversion from those
models to the actual small-etale ModuleCat sheaf functors. Those imports and transitive
proof dependencies are no longer introduced by this item. They may remain needed elsewhere;
this report does not claim whole-library unreachability.

No other original direct import or stated dependency is removed. The normalized point
equivalence, canonical sections comparison, both projection definitions and derived tensor
remain necessary. The unit `sk-prop-sf-kunneth-ordinary` has empty `realized` statement/step
lists; its route is preserved through the same geometric-fibre comparison.

## Where the brief, the DAG or earlier work was wrong

The original plan treated the general ringed-topos composition theorem as directly
specializable to these actual small-etale sheaf functors. Its Lean declaration instead uses
`RingedTensorCorner`/`RingedTensorEdge` models and representative normalization data. The
necessary model identifications are not among the item's existing declarations. The already
proved abstract projection-mate theorem gives a shorter route and makes that conversion
unnecessary, but it exposes the missing tensor-normalization input explicitly.

The new normalization equation is a genuine independent result from the proof of Stacks
07A4 and the normalized point equivalence of 04JQ/0F0F. It is not the projection square
under another name. Searches of Mathlib (LeanFinder, Loogle, grep and LeanSearch), the project
source and DAG found no existing declaration of this equation. The nearest blueprint
ancestor is `lem-kun-0f0f`; blueprint searches found no duplicate of this tensor-only result.
No existing statement is disputed or weakened, and no consumer adaptation is required.

## New nodes

`lem-kun-geometric-point-pullback-tensor-normalization` records the compatibility of the
concrete pullback/stalk evaluation comparison with the canonical derived tensor constraints.
Its source is Stacks `sites-cohomology.tex`, Tag 07A4,
`lemma-pullback-tensor-product` (proof on flat K-flat representatives), with the point
normalization of `etale-cohomology.tex`, Tags 04JQ and 0F0F. Its module contains one theorem
and three concrete formula/construction helpers. The result is needed in step 1 of the
item's revised proof; the item itself and its projection maps do not occur in its statement.
No existing definition or statement was changed, so no change record is required.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
