## What changed

Replaced the sole hole in `AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`
by a complete local-to-global proof. Independent frame covers of F and G give the
cover by their pairwise intersections; its joint surjectivity is proved pointwise.
The compact-support compositor, product coefficient transport, product exchange,
identity pullback comparison and the existing normalized heart identification give
an explicit isomorphism from the common source to a single degree-zero sheaf.
The existing `derived_eq_of_cover` helper then descends equality of the restrictions.

Added one proof import, `Sheaf.AlgebraicGeometry.VectorIntegrationDirectSumLocal`.
Its single theorem isolates the calculation on one common frame open. The local
statement only concludes equality after restriction to W and requires actual
frames on opens containing W; it contains no covering or global descent assertion.
It assumes the projection's invertibility, already proved in the item. Its map parameters are constrained by explicit equalities to the existing
constructions; local `let` terms name only the base bundle objects. This avoids
comparing expanded exchange and coefficient terms during descent. There is no
circular import and no duplicate public definition. All existing signatures, definitions,
public imports and previously completed proofs are preserved.

Local irreducibility attributes keep the underlying bundle projections, bundle
schemes, derived functors, inverse-image comparisons and the compact-support
projection map from expanding during
elaboration. These are local attributes; no exported attribute or definition body
changes. The map constraints are discharged separately by the existing definitions. The
integration's defining equation is transported through the restricted compositor
with `congrArg`, avoiding broad normalization of the surrounding derived functors.
The temporary diagnostic module and profiling options have been removed.
The full item compiled successfully in 56.3 seconds with the default recursion
bound; the new local module also compiled successfully (52.5 seconds).

The DAG records this reduction and the local calculation's source proof. No change
record is needed: no existing public interface or construction changes.

## Proved and sorry left

Closed the original syntactic hole in
`AlgebraicGeometry.Etale.vectorBundleIntegration_directSum`
(node `lem-pur-vector-trace-geometric-descent`) by a compiling proof from the local
restriction theorem and the existing degree-zero descent helper.

Added one hole:
`AlgebraicGeometry.Etale.vectorIntegration_directSum_local`
(node `lem-pur-vector-integration-direct-sum-local`), whose entire proof is
`:= by sorry` in its own new module. Its docstring and node give the ordered
counit, projection and exchange argument in words.

This is a decomposition: one original hole closed, one strictly local hole added,
net zero holes closed. The item itself has zero remaining holes; the delivery has
one. No hole was added to a definition or a private helper. The other existing
clauses (base change, compactification triangle, swap, concentration, zero rank
and empty base) retain their proofs.

## No longer needed

No existing Lean import was removed and no module was withdrawn. No target-wide
pruning is claimed.

The parent node no longer directly needs the ordinary affine counit tensor
normalization, compact-projection exchange, or shriek tensor composition nodes:
these belong to the new one-open calculation and remain needed transitively.
The separate open-tensor lemma is not needed directly by the parent, whose
projection-isomorphism proof already uses the source finite projection theorem.

The former parent proof's separate symmetric-algebra-core, affine-relative-Spec
and relative-Spec-base-change dependencies are unnecessary at this level:
`VectorTraceGeometry` already supplies the actual product and pulled-back bundle
maps. Their construction is reused, including its generator specifications.
This does not withdraw or alter any upstream declaration. The corresponding
three direct dependencies are removed from the parent proof plan. The obsolete
parent tool-use approvals for these three nodes, compact-projection exchange and
the separate open-tensor lemma are also removed, preserving the order of every
remaining approval.

The DAG also no longer asks the parent to reprove frame invariance or abstract
composite-adjunction properties supplied by the imported local calculations.
Its former direct linear-trace-invariance, composite-adjunction, general
proper-coproducts projection, and general degree-zero-derived-map-gluing edges
are removed. Equality descent is proved directly from the fully faithful single
functor, `etaleDegreeZeroHomEquiv_map`, and jointly faithful inverse images;
normalization uniqueness uses the existing unique gluing theorem. The corresponding
obsolete degree-zero gluing and proper-coproducts tool approvals are withdrawn.


The ordinary Tate pullback is used by the unchanged coefficient constructions and
the local lemma rather than a separate global proof step. Its statement dependency
is preserved. All eight old parent tool-use approvals are obsolete for the direct
proof and withdrawn. None of the referenced declarations is deleted.

The exact direct proof-dependency edges removed are:

- `def-weil-pbc-composite-adjunction`
- `lem-amb-linear-trace-invariance`
- `lem-amb-proper-coproducts-projection`
- `lem-amb-shriek-tensor-composition`
- `lem-asd-compact-projection-exchange`
- `lem-asd-etale-finite-twist-pullback`
- `lem-pur-degree-zero-derived-map-gluing`
- `lem-pur-etale-open-derived-tensor`
- `lem-pur-ordinary-affine-counit-tensor-normalization`
- `lem-weil-pbc-affine-morphism-relative-spec`
- `lem-weil-pbc-quasi-coherent-symmetric-algebra-core`
- `lem-weil-pbc-relative-spec-base-change`

## Where the brief, the DAG or earlier work was wrong

No statement dispute or mathematical correction was needed. The old direct-sum
plan combined the local affine/exchange comparison with the global degree-zero
descent; these are now separate, with the latter written in Lean. Intersections
of frame opens need not be affine. Rank zero, empty opens and the zero ring are
included by the stated local unit and uniqueness arguments.

Searches: LeanFinder returned algebraic linear-map/field trace lemmas rather than
etale integration; Loogle found `Adjunction.comp_counit_app`, which only supplies
the abstract counit formula. Remote Mathlib grep found no vector-integration or
compact-support projection result. Project and blueprint searches found the
global hole and affine normalization dependency, but no existing simultaneous
frame restriction theorem.

## New nodes

`lem-pur-vector-integration-direct-sum-local`, implemented by
`Sheaf.AlgebraicGeometry.VectorIntegrationDirectSumLocal`, states the ordered
multiplication equation only after restriction to one open W lying in the two
supplied frame opens. It is the local calculation from paragraph 2 of the
vector-bundle-purity proof (geometric-descent Steps 4--6); the global covering,
degree-zero comparison and descent are proved in the item. The local node uses
only existing declared dependencies and is strictly less than the global theorem.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
