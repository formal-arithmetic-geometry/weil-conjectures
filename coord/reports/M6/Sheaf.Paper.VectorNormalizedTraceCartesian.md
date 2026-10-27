## What changed

Filled `WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_normalized_trace_cartesian`
from the existing normalized vector-purity family and its base-change theorem. Added proved
private helpers for normalization at the tensor unit, the unit equation of the source
associator, transposition of the mate square, and transport of the trace coefficient.
The theorem statement and its public import are unchanged. The extra proof imports expose
no additional interface to consumers. Updated the item's DAG proof and dependencies.

The proof first identifies the unit components of both normalized families with the
Brown adjuncts of the actual integration maps. Pullback-unit coherence and naturality
of the second family turn its exceptional exchange equation into a square of these
adjuncts. The mate counit identity gives the compact-support square. The existing
`orderedTatePullbackSquare` and naturality of exchange put this square in the displayed
total-space coefficient coordinates. All private helpers have complete proofs. The new module
`Sheaf.Paper.VectorNormalizedUnitAdjunct` proves
`WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_normalized_unit_adjunct`.
Its interface accepts the existing vector normalization directly, and retains the abstract
monoidal cache before specializing coefficients. Projection invertibility at the unit follows
from right unitality, so no general projection-formula instance is needed for that step.

## Proved and sorry left

Closed 1 of 1 direct holes:
`WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_normalized_trace_cartesian`
(node `lem-pur-vector-normalized-trace-cartesian`). No direct `sorry` remains in the item.
Added 0 holes and split off 0 remaining proof obligations. The new unit helper is proved.
The proof uses already stated dependencies,
including the normalized family, its base-change law, and ordered Tate square; it does
not claim to close their separate obligations.

Compilation: the first delivery compile exceeded 60 seconds in the concrete-coefficient
proof. The trace calculation now runs in a private theorem over an abstract finite
commutative ring, then specializes once to the project's coefficient ring. Profiling
of the artifact-producing compile showed 20.1 seconds of kernel checking for this helper
and 8.91 seconds for the public specialization. Profiling options were removed afterwards.
The target signature remains unchanged. The unused zero-preservation binder is retained,
with the unused-variable linter disabled only for this theorem; its argument covers the
more general Cartesian presentation supplied by the existing base-change law.

## No longer needed

The planned proof dependency `lem-pur-integration-unit-normalization`
(`Sheaf.Paper.IntegrationUnitNormalization`) is unnecessary here: the normalization
uses the ordinary projection, whose existing `projectionMap_rightUnitality` directly
gives the required unit calculation. No import of that module was added.

The direct planned dependency `lem-asd-etale-finite-twist-pullback`
(`Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`) is replaced in this item's proof
by the existing `lem-pur-ordered-tate-pullback-square`
(`Sheaf.Paper.OrderedTatePullbackSquare`), which supplies exactly the coefficient
transport equation. The latter's own dependency on finite twist pullback remains.
No existing module is withdrawn, and no global pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original DAG step mentioned the coefficient-first integration unit lemma even
though `VectorPurityGammaNormalized` uses the ordinary, coefficient-last projection.
Its unit calculation is performed directly with that projection's right-unit law.
The existing Tate square lemma suffices for the coefficient calculation; no further
split is needed. The argument applies uniformly in rank zero and over empty schemes.
The hypothesis preserving zero is retained unchanged, though the supplied general
purity base-change equation already covers every Cartesian bundle presentation.

## New nodes

`lem-pur-vector-normalized-unit-adjunct`, realized by the proved unit-identification theorem
in `Sheaf.Paper.VectorNormalizedUnitAdjunct`. This is the single-bundle unit component
of the argument; it contains no Cartesian square or base-change claim. It adds no hole.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
