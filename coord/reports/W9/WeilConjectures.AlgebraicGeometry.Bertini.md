## What changed

The source module WeilConjectures.AlgebraicGeometry.Bertini now proves its existing theorem
from a single smooth dimension-cut statement and the existing finite-field descent theorem.
All original signatures, public imports, attributes and definition bodies are preserved.
Proof-only imports provide the new cut, descent and smooth-relative-dimension base change.

A proved private helper performs strong induction on every positive relative dimension.
Its base case uses the identity immersion and the identity-pullback isomorphism. Its step
chooses lifts of the prescribed sections, takes their finite image, verifies their structure
map equations, applies induction to the finite étale pullback cover, composes the closed
immersions, and transports connectedness along pullbackLeftPullbackSndIso. These choices are
inside a theorem proof; no definition chooses data from an unproved existence theorem.

A second proved private helper constructs the finite-field datum for the supplied k₀ and
its algebraic closure. It applies the existing closed-subscheme descent theorem and proves
that its geometric Frobenius equals the source's geometric Galois Frobenius by comparing
both pullback projections. This preserves exactly the target's automorphism equation.

The new module Sheaf.AlgebraicGeometry.BertiniFiniteCoverDimensionCut states one simultaneous
smooth/irreducible hypersurface cut. Its source, full argument in words and DAG node retain
the existing prescribed-point smooth-system and finite-cover irreducible-system inputs.
The parent DAG now records the actual induction and descent argument.

The read-only downstream query found 25 transitive consumers. They retain exactly the same
public theorem and public imports; no consumer adaptation is needed.

## Proved and sorry left

Original holes: 1. Closed in the item module:
AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback.

New holes: 1, in AlgebraicGeometry.exists_smooth_finiteCover_dimension_cut
(node lem-zl-bertini-finite-cover-dimension-cut), in its own new Sheaf module.
There are zero holes left in the item module and one in the delivery as a whole.
This is a decomposition (one upper hole closed and one strictly smaller lower hole added),
not a net proof gain. The private induction and descent-comparison helpers contain no holes.

## No longer needed

No existing imports are removed. No existing declaration, module or mathematical dependency
is withdrawn. The parent no longer directly cites lem-zl-bertini-prescribed-point-smooth-system
or lem-zl-bertini-finite-cover-irreducible-system: both are preserved as proof dependencies
of the new single-cut node. The finite-field descent node remains a direct dependency.
The integral dimension-cut and smooth-curve interpolation modules found during search do
not preserve a connected finite étale cover and are not imported. No unit route is bypassed.
Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The existing plan is mathematically sound. Its description of iteration as elementary hides
substantial Lean glue: prescribed sections must be lifted and their finite image formed,
and the iterated pullback cover must be transported through its canonical isomorphism.
That glue is now proved. The two existing linear-system interfaces use different basis and
tensor-pullback presentations; assembling them, obtaining the projective closure and
converting smooth pure dimension to smooth relative dimension remain in the single-cut
lemma. This delivery does not silently assume those conversions.

The current blueprint moved this proof to sk-lem-wgen-bertini-cover; the new node's source
uses literature/blueprint/latest and its actual path. The existing node's unit and other
maintainer fields are preserved. No returned repair applies to this item.

## New nodes

lem-zl-bertini-finite-cover-dimension-cut states a single cut in dimension d ≥ 2 over an
arbitrary algebraically closed field, with affine connected source, smooth relative
dimension d−1 and connected inverse image. Its two non-elementary inputs are the existing
smooth-system and finite-cover irreducible-system nodes. It omits both dimension iteration
and descent, so is strictly part of the original argument. Its edge cases include d=2,
a singleton prescribed set and the identity cover. Rational points have closed reduced
images; vanishing on these images supplies the required factorization of their morphisms.
A connected finite étale cover of connected X is nonempty and surjective. Finite affine
smoothness gives the finite-type hypotheses used by the stated systems. Searches found
no duplicate single-cut theorem. No definition or existing interface changes; no forced
adaptations or change records are needed.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
