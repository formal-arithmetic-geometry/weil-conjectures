## What changed

Proved `AlgebraicGeometry.cotangent_surjective_of_tangent_injective` with its signature
unchanged. Added a private proved helper converting the bijective scheme residue-field
map hypothesis into bijectivity of the structural map from the ground field. This uses
`Scheme.residue_residueFieldMap`, the stalk isomorphism at the unique point of a field
spectrum, and surjectivity of the residue quotient.

The main proof follows the existing two-step DAG plan: apply
`AlgebraicGeometry.rational_tangent_cotangent_duality`, transfer tangent injectivity
through its two linear equivalences, and apply `LinearMap.dualMap_injective_iff`.
Finally, its formula on maximal-ideal representatives identifies the surjective linear
map with the statement's `Ideal.mapCotangent`. Proof irrelevance identifies the two
bijectivity witnesses used by `schemeTangentMap`.

Added the proof-only import `Mathlib.LinearAlgebra.Dual.Lemmas`. The existing private
import of `Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality` is used. All public
imports and declaration signatures are preserved. No new public declarations or nodes. The unused-variable linter is disabled locally
for the theorem because its unchanged closed-point hypotheses are not needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.cotangent_surjective_of_tangent_injective`
(node `lem-sc-point-tangent-cotangent-surjective`).

Holes added: 0. Holes remaining in the delivered module: 0. Split off: 0.
The private helper `structural_residue_bijective` is fully proved.

## No longer needed

None. Both declared proof dependencies are used: rational tangent-cotangent duality
and the Mathlib leaf for dual-map injectivity iff surjectivity. No imports, nodes or
modules are pruned; the unit route and existing DAG proof remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The locally finite type and closed-point
hypotheses are stronger than the proof needs, as already noted in the DAG review;
they remain unchanged. The rationality interfaces differ between the item and its
duality dependency; the private helper supplies their compatibility rather than
changing either public interface.

Read Stacks `varieties.tex`, `lemma-tangent-space-rational-point` and
`lemma-map-tangent-spaces` (Tags 0B2E and 0B2F). Loogle located the exact Mathlib
linear-algebra lemma; LeanFinder returned cotangent-complex lemmas rather than a
shorter scheme-level theorem. Source searches found the already-proved duality
statement. No new statement requiring edge-case validation was introduced. The
argument applies also to zero cotangent spaces, without finite-dimensionality.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
