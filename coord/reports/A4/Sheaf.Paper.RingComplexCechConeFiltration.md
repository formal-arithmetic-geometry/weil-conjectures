## What changed

Replaced the sole proof hole in
`AlgebraicGeometry.ringComplex_cech_cone_filtration` by a complete proof.
The theorem's statement, visibility, docstring and two public imports are unchanged.
Added proof imports for the already proved bounded-complex devissage, the existing
constant-module functor and point-lift API, concrete module products, and Mathlib's
short-exact-sequence triangles. Added only proved private helpers in the assigned
module: pointwise linear equivalences give sheaf isomorphisms, pointwise criteria
for zero objects and invertibility, and finite localization-term membership.
No other Lean module, statement or definition was changed.

Choose a finite generating family and its augmented ordered model. The degree-zero
augmentation is invertible and the remaining targets are zero, so the augmentation
is epi. Its categorical kernel is zero in degree zero, agrees with the model in
positive degrees, and is supported in [1,r]. Each positive term is a finite product
of away localizations with an invertible ideal element. The existing additive
constant-module functor, the degree-zero single functor and Q preserve these finite
products. Apply the proved bounded devissage to the kernel. Rotate its short exact
sequence triangle and compare it to the augmentation cone triangle; then transport
across the augmentation-compatible derived model isomorphism.

Updated the assigned node's proof, proof_deps and proof_origin to describe exactly
this argument. In particular it uses the existing short exact sequence triangle
Mathlib leaf and explicitly records the constant-module and point-lift APIs.

Validation: the final single-file server compile passed with exit code 0 in
14.0 seconds, with no warnings. The theorem signature was compared textually
against the current source and is identical. All lines are at most 100 characters.
The updated dependency paths were checked for cycles; none return to this node.
The delivery tool additionally runs its compile and axiom probe.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ringComplex_cech_cone_filtration`
(node `lem-weil-pbc-ring-complex-cech-cone-filtration`).

There are zero remaining holes in the assigned module and zero added holes.
No statement is split off. All private helpers are proved. The bounded devissage
used by the proof is already proved. No object is selected from an unproved
existence assertion: the model is supplied by the theorem's hypothesis, the kernel
is a categorical limit, and triangle comparison uses Mathlib's proved triangle
completion and isomorphism results.

Edge cases: r=0 gives the empty support interval [1,0]; terms above r are zero
because an increasing embedding from a larger finite ordinal cannot exist.
No nonzero-ring or nonnilpotence assumption occurs. Zero and nilpotent products
produce zero away localizations; invertibility still gives bijective scalar
multiplication there. Repeated generators cause no exception. No positive
localization term needs the differential-coordinate formulas.

## No longer needed

No existing import was removed, no module is withdrawn, and no globally pruned
node is claimed. Every original declared proof dependency is still used:
the model predicate, the abstract derived category, triangulated closure, and
bounded-complex termwise devissage.

The explicit identity-pair cancellation and residual cone differential from the
old proof plan are unnecessary. The augmentation's categorical kernel and its
rotated short exact sequence triangle supply the same shifted positive tail.
The alternating differential formulas and localization transition maps are
unpacked from the model but unused; a chain map with the stated term coordinates,
negative vanishing and degree-zero normalization suffices. No orthogonality,
localization-flatness, K-flat resolution, scalar-extension comparison, or
Godement-resolution theorem is used. The Godement construction module is imported
only for its existing constant-module functor and additive instance; the
semilinear-extension module only for the point lift and pointwise morphism
extensionality. These imports add no new proof obligations.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and original plan are sound. The plan's cancellation
step need not be implemented by an explicit cone homotopy or a new residual
complex: the kernel short exact sequence and triangle comparison give the needed
cone isomorphism. This avoids another decomposition of the obligation.

The proof remains inside the existing unit route. No target signature, source
library declaration, public definition, or consumer interface changed, so no
change record or consumer adaptation is needed. The two newly recorded helper
nodes are existing construction interfaces, not new or assumed theorems.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
