## What changed

Replaced the item's hole by a proof composing two independent finite-diagram
comparisons. The first comparison works over the inverse image of the constant
algebraic completion ring. The second compares this with the actual relative
completed realization and has no tower M, local-system, effectivity, boundedness
or finiteness assumption on E.

Added ConstantAdicFiniteDiagramData with actual completion evaluation maps,
their cone, inverse-image finite projections, an all-pairs projection equation,
exactness of constant module sheafification, and the constant algebraic derived
realization. These constructions are explicit and contain no holes. The main
proof transports finite lissity by the homology isomorphisms and composes the two
forward squares using associativity and functoriality of scalar restriction.
Existing signatures and public imports of the item are unchanged. No existing
module or node besides the item was changed.

Validation: all four modules compiled on the server; the data module took 8.0 s,
the scalar comparison 9.5 s, the local constant diagram 9.7 s, and the item 14.7 s.
The original theorem signature was checked byte for byte against the source.
The unused-variable linter is suppressed locally for the original theorem because
its unchanged statement names three proof binders that the conclusion does not use.

## Proved and sorry left

This is a decomposition, not a completed mathematical proof of the original
obligation. One original hole was replaced by two strictly separated obligations;
net holes closed minus added is -1.

Original hole closed by composition:
AlgebraicGeometry.Scheme.lisse_tower_local_algebraic_reduction_diagram
(node lem-weil-pbc-lisse-tower-local-algebraic-reduction-diagram).
The item itself has zero remaining holes.

Two holes added, one in each new statement module:

- AlgebraicGeometry.Scheme.lisse_tower_constant_algebraic_reduction_diagram
  (node lem-weil-pbc-lisse-tower-constant-algebraic-reduction-diagram): local finite
  diagrams and their effective cones over the constant algebraic completion ring;
  it makes no assertion about a completed sheaf or completed realization.
- AlgebraicGeometry.Scheme.completed_constant_unbounded_finite_diagram_comparison
  (node lem-weil-pbc-completed-constant-unbounded-finite-diagram-comparison): the
  scalar comparison for arbitrary E, independent of M and its local lissity.

Proved in ConstantAdicFiniteDiagramData:
constantAdicCompletion_eval_step, constantAdicFiniteProjection_comp, and
constantAdicFinite_constant_exact. The private relativelyFiniteLisse_of_iso and
paste_reduction_squares in the item are also proved. No axiom or hole in a
definition was added.

## No longer needed

No module is withdrawn or globally pruned. No existing public import is removed.
The item's direct proof dependencies are now the two new comparison statements
and the existing bounded-constructible-tower definitions. Its former finite
origin, stalk, local-constancy and compatible-trivialization dependencies remain
needed by the constant-ring statement, rather than being declared unnecessary.
The canonical tensor/pullback and finite-complex completed-realization results
remain dependencies of the scalar comparison. No original mathematical
dependency is certified globally unnecessary. The
standalone ConstantCompletionEquivalence theorem is not applied directly, but
its module remains in transitive imports of the existing completion infrastructure.
No global unreachability or module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan combined a finite local-system argument with an unbounded
completed-realization comparison in a single hole. The existing
completed_constant_finite_complex_realization interface concerns bounded finite
complexes; it cannot be applied directly to the unrestricted E in this item.
The new scalar statement records precisely the additional K-flat finite-diagram
comparison required for arbitrary E. Both new statements retain the actual
coefficient rings and all-pairs forward semilinear equations. The two reduction
sources differ: one is the inverse-image constant algebraic ring, and the other
is the inverse image of the actual completed coefficient sheaf. The composition
proof bridges these two sources explicitly.

Edge cases checked when stating the new obligations: empty schemes use the empty
cover; levelwise bounds remain nonuniform; the zero complex and unit ideal give
zero finite levels; equal indices are included in every projection and transition
equation; the scalar statement does not assume boundedness or finite Tor dimension.

## New nodes

- def-weil-pbc-constant-adic-finite-diagram-data: explicit constant-ring coefficient
  cone and derived realization, sourced in Tags 06YY and 093J--093M. Its auxiliary
  equations are proved, with no new hole.
- lem-weil-pbc-lisse-tower-constant-algebraic-reduction-diagram: finite local tower
  presentation, using Tag 09BV's derived local-constancy and simultaneous
  trivialization argument, before any completed realization.
- lem-weil-pbc-completed-constant-unbounded-finite-diagram-comparison: finite
  tensor comparison for arbitrary K-flat resolutions, using Tags 06YY, 06YU and
  093J--093M. This has no hypothesis concerning a local-system tower.

LeanFinder, Loogle, Mathlib grep, repository searches, and the blueprint search
were run. Completion evaluation formulas were found and used in the explicit
cone proof; no existing theorem supplied either new comparison interface.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
