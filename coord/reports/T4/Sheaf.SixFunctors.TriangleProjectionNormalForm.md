## What changed

Prove the finite coefficient clause of
`AlgebraicGeometry.ProEtale.AmbientProperOpen.triangleProjectionNormalForm`, using
`properOpenProjectionMate`, naturality of the mate across the pullback-square
isomorphism, and first-variable projection naturality. The proved finite diagram
chase works over every finite commutative ring and is specialized to the positive
quotient coefficient ring.

Extract the genuinely separate intrinsic-system clause into
`Sheaf.SixFunctors.TriangleProjectionSystemNormalForm`. Move the two Noetherian
instances and four system definitions there without changing their signatures or
bodies, and publicly re-export them from the parent. The parent theorem's statement
is unchanged. No module or declaration is withdrawn. The definition move is recorded
in `coord/changes/T4-triangle-projection-system-clause.md`.

## Proved and sorry left

Closed upper hole:
`AlgebraicGeometry.ProEtale.AmbientProperOpen.triangleProjectionNormalForm`
(`lem-sf-triangle-projection-normal-form`), from one to zero holes in the item module.
The finite clause is completely proved; the combining proof is complete.

Added and remaining:
`WeilConjectures.IntegralSystemRealization.triangleProjectionSystemNormalForm`
(`lem-sf-triangle-projection-system-normal-form`), exactly one `sorry` in the new module.
This is a decomposition: one upper hole closed, one strictly smaller system-only hole
added, net zero hole reduction. No private declaration or definition has a hole.
The existing `properOpenProjectionMate` dependencies remain separate project items.

## No longer needed

Remove the proof-only import `Sheaf.Paper.RingedProjectionTensorComposition` and
its direct proof dependency `lem-sfb-ringed-projection-tensor-composition`:
first-variable naturality is already a field of the published projection natural
transformation. Its general coherence theorem remains in the library.

The parent no longer separately applies `lem-sf-ambient-proper-open-pasting`,
`lem-sf-open-tensor-normalization`, or `lem-coef-semilinear-derived-sections` in its
proof: the concrete definitions and projection-mate theorem already fix the
operations. They remain statement dependencies and public prerequisites. Remove
obsolete top-level tool approvals for open normalization, ringed coherence and
semilinear sections; retain the Noetherian tools in order. No whole module is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned argument suppresses the pullback-square comparison; the finite Lean
proof retains it explicitly, using mate naturality at a.inv followed by delta_j.
No projection transformation is inverted. No mathematical statement was found false.

The intrinsic-system categorical chase elaborates to a complete term, but the
concrete system word conversion repeatedly exceeds the 60-second compiler limit.
Profiling confirms that the finite clause kernel-checks quickly. Attempts included
explicit intermediate types, generic projection-naturality and tensor-cancellation
helpers, direct and curried square transports, explicit derived-localization
instances, proof-irrelevant square sharing, generic word definitions and a bundled
diagram. None yielded a fully checked system proof; all those experiments are
excluded from the delivery. The separate system-only result is a genuine clause of
the argument, has no finite coefficient assertion, and has a complete proof plan.
The unit has no realized statement or steps to bypass. Edge cases checked in the
argument: identity maps, zero inputs, empty schemes, and the positive level n=0.

## New nodes

`lem-sf-triangle-projection-system-normal-form` records the intrinsic-system clause
and its unchanged system definitions. It uses the existing system projection-mate
identity and two naturality steps before evaluation or total limit. Its Lean module
is `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm`. The parent node now applies
this result only for its second conjunct. Change record:
`coord/changes/T4-triangle-projection-system-clause.md`.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
