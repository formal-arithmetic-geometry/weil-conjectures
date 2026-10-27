## What changed

Filled `LinearMap.invertible_relation_minor_generators` in
`Sheaf.RingTheory.InvertibleRelationMinorGenerators`. Two proved private helpers expand a
linear map in the coordinate generators and apply the adjugate to a row relation.
The original public theorem signature, definitions and public imports are unchanged.
Added the private proof import `Mathlib.CategoryTheory.Functor.EpiMono` for the explicit
adjunction-to-epimorphism-preservation theorem.

The algebraic argument proves the determinant identity, solves it with `invSelf`, and
expresses each localized fraction in the span of the last generators. The sheaf argument
uses epimorphism cancellation: agreement on the last sections gives agreement on the first
by the adjugate relations and invertibility of the determinant on every smaller open.
The tilde and restriction left adjoints send the original surjection to an epimorphism.
Decomposing that surjection into coordinate maps completes the cancellation argument.
The node's third proof step and proof origin now record this categorical route.

## Proved and sorry left

Closed: `LinearMap.invertible_relation_minor_generators` (one original hole).
Added holes: none. Remaining holes in the delivered module: zero.
Both private helpers are proved. No new axioms or unproved dependencies are introduced.
Validated by the server single-file Lean compile (22.3 seconds); removed its one reported
unused tactic before the delivery preflight recompilation.

## No longer needed

No imports, nodes or modules removed. All six original proof dependencies remain used.
Added the existing Mathlib leaf `lem-weil-pbc-affine-tilde-gamma-adjunction` to the node's
proof dependencies to record the tilde adjunction used by the shorter sheaf argument.
The explicit maps to localizations at products and the basis-open local-lifting construction
of the old third proof step are unnecessary; the same sheaf-generation conclusion follows
by cancellation of the restricted tilde surjection. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing third proof step can be shortened categorically.
The argument requires no assumptions excluding zero determinant, zero ring, a = 0 or b = 0.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
