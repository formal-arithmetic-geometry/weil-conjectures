## What changed

`Sheaf.Paper.SystemProjectionFormulaCoherence` reduces its remaining
`projection_evaluation` hole to the finite evaluation of the specified pullback
compositor. The proper counit projection and open-unit tensor comparison are
calculated by adjunction transposition. Naturality of the existing evaluation
comparisons pastes these calculations with the final pullback identification.
The proper calculation permits a comparison on its first finite input; the open
calculation permits a comparison on its second finite input. These endpoint
comparisons are exactly the open-extension and proper-pullback evaluations
required for the compactification word.

Private category lemmas prove adjunction transport, tensor interchange, and
support-word pasting before they are instantiated with the sheaf operations.
This avoids repeatedly unfolding the derived-functor constructions. The private
isomorphism proof for the compact-support compositor is first proved with an
arbitrary compatible triangle and then instantiated with the canonical triangle,
so instance search does not expand the compactification construction.

A private bifunctor isomorphism exposes naturality of the existing
`canonicalFinitePullbackTensor`. Its component equations are proved, and its
components are the original construction. No existing definition, public theorem
signature, or public import changes. The preexisting composition-coherence and
joint-naturality proofs are retained. No adopted-source file changes.

The complete module compiles: the final profiling run took 42.3 seconds, within
the per-file limit. The new leaf also compiles. Eliminating the compactification
factorization equality before the calculation avoids expensive kernel conversions
between two presentations of the inverse-image functor; the isolated evaluation
proof kernel-checks in under one second. The refinement isomorphism passes the
proper/open isomorphism proof explicitly. All profiling and diagnostic options
are removed from the delivery sources. Public signatures, existing definition
bodies and public imports were compared with the published source and agree.

## Proved and sorry left

Original holes: 1. The upper hole
`WeilConjectures.SystemProjectionFormula.projection_evaluation` is closed by
**decomposition**, not counted as an independent complete proof. Its remaining
argument is isolated as the strictly smaller theorem
`WeilConjectures.IntegralSystemRealization.systemPullbackCompositorEvaluation`
in the new module `Sheaf.Paper.SystemPullbackCompositorEvaluation`, attached to
`lem-pur-system-pullback-compositor-evaluation`.

Holes closed: 1 (`projection_evaluation`). Holes added: 1
(`systemPullbackCompositorEvaluation`). Holes left in the item module: 0.
Holes in the delivery: 1; net change: 0. All private helpers are proved.
The existing imported `projection_change` and `projection_triangle` obligations
are unchanged and are not new holes of this delivery.

The new statement only compares inverse image and its composition under finite
evaluation. It has one input and no tensor product, compactification, projection
mate, open extension, proper direct image, or inverse limit in its conclusion.
It is one factor of the original proof, not the original statement under another
name. The combination of factors is actual Lean in the assigned module.

Edge cases were checked in the argument: n=0 is the positive exponent one;
identity maps give the usual unit comparisons; zero inputs give zero-object
maps. Both projection calculations work on arbitrary system inputs, including
non-normalized ones, and the original public domain hypotheses are retained.
The inverse of the finite open tensor map is used only after its isomorphism
property is proved by transport of the system open comparison. No faithfulness
of finite evaluation is assumed.

## No longer needed

No module is withdrawn, and no original import is removed. The existing private
proof imports are all used by the retained coherence proof. The new proof import
is `Sheaf.Paper.SystemPullbackCompositorEvaluation`.

The parent proof no longer directly calls the generic existence result
`lem-coef-semilinear-derived-sections`: its needed unit and counit equations are
already fields of `Operations`, and the transpose calculation is proved here.
The obsolete proof dependencies and tool-use approvals for
`lem-coef-semilinear-derived-sections` and `def-exchange-projection` are removed
from the parent proof record. Both nodes remain statement dependencies or source
specifications where appropriate. No claim of global unreachability is made.
The tensor evaluation theorem is retained through
`def-pur-completed-pullback-tensor-comparison`. The unit route and the old
composition proof dependencies are preserved. No separate appeal to
`lem-sf-open-tensor-normalization` is needed for the evaluation square: the
finite open tensor inverse is proved invertible by transporting the supplied
`OpenComparisons.projection` isomorphism. This is a local proof simplification,
not a claim that the normalization node is globally unused.

## Where the brief, the DAG or earlier work was wrong

The old finite-evaluation proof plan did not name a declaration comparing
`Compositors.pullComp` with `sfIntrinsicDerivedPullbackComp` under the specified
evaluation maps. The existing `ordinaryCompositionEvaluation` covers its
ordinary part, but does not state the derived identity for these particular
section-normalized compositors. `NormalizedPullbackCompositionTransport` uses
different named comparators and additional realization data; it cannot be
applied directly to arbitrary `Compositors` without this identification.
The missing normalization step is now stated explicitly with its source,
complete proof in words, and Lean attachment. Nothing is marked disputed.

## New nodes

`lem-pur-system-pullback-compositor-evaluation`, in
`Sheaf.Paper.SystemPullbackCompositorEvaluation`, states the inverse-compositor
finite-evaluation square for arbitrary strict systems. Its proof identifies
ordinary compositors by their section and conjugacy equations, reuses
`ordinaryCompositionEvaluation`, transports through the intrinsic finite
realizations, and localizes the cochain normalization square. It is independent
of the parent: a source-only traversal of all statement and proof dependencies
found no path back to the parent. The node records actual LeanFinder, Loogle,
Mathlib grep, and LeanSearch queries. The blueprint search found no exact match.

There is no statement or definition change record: all existing signatures and
all six existing definition bodies in the assigned module are unchanged.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
