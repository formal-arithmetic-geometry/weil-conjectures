## What changed

The statement and public imports of
`Sheaf.AlgebraicGeometry.ProjectiveLineAutomorphismHyperplane` are unchanged.
Its theorem `AlgebraicGeometry.ProjectiveLine.automorphism_hyperplane` now has a
complete Lean proof from the two new proof imports below. Private proved helpers
identify Picard pullback of an invertible module and construct the induced
projective-line automorphism after any base change. The latter constructs both
maps and checks their inverse laws with the projective-space pullback square.

`Sheaf.AlgebraicGeometry.ProjectiveLineAutomorphismOverField` proves
`AlgebraicGeometry.ProjectiveLine.automorphism_twist_one_over_field` from the
existing `existsUnique_degree_of_isInvertible` and the proved monomial cohomology
API. The dimension of global sections determines the integer degree directly:
it is zero for negative degree and d+1 for nonnegative degree, and must equal two.
This avoids the planned intermediate argument about automorphisms of Z.

For a general base the main proof shows that `a*H * H⁻¹`, with H the actual O(1)
class, is trivial on every residue-field fibre. It then applies the new generic
kernel theorem in `Sheaf.AlgebraicGeometry.ProjectiveLineFibrewiseTrivialDescent`
and cancels H. The remaining theorem concerns arbitrary invertible classes and
contains no automorphism or hyperplane-preservation assertion.

All three modules compiled cleanly together through lcompile: the field module
in 14.0 seconds, descent in 3.3 seconds, and the item in 20.0 seconds. The subsequent
import cleanup is checked again by compilation and the delivery preflight.
Only the assigned existing module and node, plus these two new modules and their
nodes, are changed. There are no definition, signature, instance, attribute or
consumer changes, and no arbitrary data chosen from an unproved existence theorem.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProjectiveLine.automorphism_hyperplane`
(node `lem-sfb-projective-line-automorphism-hyperplane`). Its body has no sorry.
Also proved the new
`AlgebraicGeometry.ProjectiveLine.automorphism_twist_one_over_field`
(node `lem-sfb-projective-line-automorphism-over-field`), with no new hole.

Added exactly one hole:
`AlgebraicGeometry.ProjectiveLine.exists_base_class_of_fibrewise_trivial`
(node `lem-sfb-projective-line-fibrewise-trivial-descent`). Its whole proof is
`by sorry`; there are no holes in private helpers or definitions. Thus this is a
decomposition, one original hole closed and one lower hole added, rather than a
claim of a net sorry reduction. There is one sorry in the delivered Lean files.
The existing field classification theorem used by the field proof still has its
own unchanged sorry; it is an intended stated dependency, not a new hole here.

The residual descent is specifically the degree-zero part of projective-bundle
Picard classification. To close it from that declaration one must implement the
free-rank-two model transport, compare its tensor pullback with the standard
projective-space base change, read off degree zero on each residue-field fibre,
and normalize the glued constant-zero twist. The current classification API
provides these ingredients abstractly but no concrete Picard kernel corollary.
Its full argument is recorded in the new theorem docstring and node. This splits
off a genuine descent step after completing the separate field degree argument.

## No longer needed

No original public import was removed and no existing module is withdrawn or
claimed to be globally pruned. The new descent signature uses only projective
space, Picard groups and residue fields; it does not publicly import projective
twists. The field proof needs its four private proof imports for classification,
TwistData, monomial cohomology and invariance of finrankH under an isomorphism.

The original node's direct proof dependencies on quotient geometry and
projective-bundle Picard classification move into the genuine descent step;
they remain needed there and are not pruned. The monomial cohomology dependency
moves into the field lemma, where the concrete P1 cohomology API is used.
The original ±1 integer multiplier argument, use of the inverse action on Picard
groups, and normalization of a globally glued degree-one twist are unnecessary
for the main Lean proof. The inverse scheme map is still used solely to construct
the fibre automorphism. No dependency of the unit's own route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target statement changes. The original plan's
±1 detour is longer than necessary: h0 of O(d) already determines d=1.

The field classification and projective-bundle Picard classification are generic
tools from another unit. The former is used as a black box only for invertible
modules on P1 over a field; the latter is the existing planned input for the
residual degree-zero descent. No result of the diagonal-trace unit supplies these
tools. Maintainer tool approvals are not added or changed by this delivery.

The blueprint ancestor helper cannot follow module-valued `created.item` fields
in this chain. For the new nodes I followed the existing explicit blueprint
pointers through `lem-sfb-diagonal-trace-diagonal-pic` to the imported node
`det-prop-diagonal-tower-trace`, paragraph (2), with the intermediate nodes in
`via`. Blueprint and local DAG searches found no duplicate of either new
statement. `lem-sfb-projective-line-twist-rigidity` has no Lean attachment and
states a different assertion involving a generically nonzero morphism; it does
not replace the proved field automorphism lemma.

Sources checked: EGA II Remark 4.2.7, printed page 75 (PDF page 72), and Stacks
Tag 0BXJ (`divisors.tex`, `lemma-Pic-projective-space-UFD`) and Tag 0B8W
(`limits.tex`, `lemma-descend-invertible-modules`), and Tag 01XS
(`coherent.tex`, `section-cohomology-projective-space` and the monomial lemma
`lemma-cohomology-projective-space-over-ring`). EGA's cited classification is
locally Noetherian; arbitrary bases here are covered by the already stated
general classification, whose proof includes approximation and limit descent.
Tag 0B8W alone does not assert projective-space Picard classification.

Edge cases checked mathematically: the field proof works in every characteristic
and does not require algebraic closure; the descent statement includes empty,
disconnected and nonreduced bases. It tests all residue-field fibres, not only
closed or generic points. Over a field its hypothesis forces the unit class;
for the empty base the degree function and all Picard classes are unique.

## New nodes

`lem-sfb-projective-line-automorphism-over-field` records the proved field step,
with the exact Lean statement, source, monomial dimension calculation and three
logged kinds of Mathlib search. It is a separate reusable theorem and adds no
sorry.

`lem-sfb-projective-line-fibrewise-trivial-descent` records the remaining generic
degree-zero descent step, with its exact Lean statement and complete proof plan
from the existing quotient geometry and projective-bundle classification. Its
Mathlib searches are logged LeanSearch, LeanFinder and grep queries. It is the
only split-off hole. There are no change records because no existing definition
or statement was changed.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
