## What changed

Replaced the hole in `AlgebraicGeometry.Etale.presentedFiniteP1Counit_baseChange`
by the forward projection, coefficient trace, tensor naturality and cancellation
argument. The statement and existing docstring are unchanged. The theorem signature was
compared verbatim with the shared source; all three node attachments match the
Lean statements, and their proof dependencies match the recorded proof steps.

Added `Sheaf.SixFunctors.ProperOrderedProjectionExchange` for the general forward
ordered projection equation, using the already proved coefficient-first compact
projection/exchange theorem. This result has arbitrary source coefficients and no
trace or projective-line assumptions. Its proper coincidence and coefficient
naturality identifications are explicit private proofs. The new general module
imports the ordinary projection and compact-support interfaces directly, without
importing the projective-line trace model. Generic categorical pasting lemmas assemble its
proper-coincidence and coefficient-naturality squares directly. The component
proof uses the recorded functors explicitly to avoid costly unfolding of local
functor aliases. No custom certificate tactics are used.

Added `Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange` for the remaining
coefficient trace transport square. This is strictly smaller than the original
obligation: it concerns only the shifted line, not an arbitrary complex, and it
contains no ordered projection, tensor trace, counit or exceptional adjunction.

The item proves tensor-trace compatibility from the coefficient equation and the
existing right-unit equation `finiteTwistDerivedEvaluation_pullback`. It proves
that forward ordered projection followed by the constructed counit is tensor
trace. Precomposing by that invertible forward projection reduces the desired
counit equation to the two forward squares.

Private helpers first combine the squares for an arbitrary coefficient object and
trace. They keep exchange and counits as natural transformations until taking
components. A final wrapper makes the underlying derived-category types explicit
while its functors are abstract. This avoids unfolding the concrete derived
pullback during category-alias comparisons; it changes no definition, statement,
assumption or mathematical dependency. All these helpers are fully proved in the
item module.

Validation: the final three-file sandbox compile passed without profiling options
or raised limits. The coefficient-trace module compiled in 25.8 s, the general
projection module in 19.4 s, and the item module in 36.0 s. All are below the
60-second file limit. No temporary diagnostic module is included.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.presentedFiniteP1Counit_baseChange`.

The general forward equation
`AlgebraicGeometry.Etale.properOrderedProjection_exchange` and all private helpers
are proved.

Added one hole:
`AlgebraicGeometry.Etale.presentedFiniteP1Trace_exchange`, node
`lem-asd-presented-projective-line-coefficient-trace-exchange`.
This is a decomposition (one original hole closed, one strictly smaller hole
added), not a net decrease of the hole count. The item module has zero holes.
There are no holes in definitions and no new axioms.

## No longer needed

No existing import was removed and no module was withdrawn. The original direct
proof dependency `lem-weil-pbc-ringed-exchange-tensor-coherence` is replaced by the
proved ordinary etale coefficient-first API
`compactProjectionMapCoeffFirst_baseChangeMap` from
`Sheaf.AlgebraicGeometry.CompactProjectionExchange`. The broader ringed-topos
square remains needed through the existing compact-projection proof; only the direct
dependency of this item is replaced, and no withdrawal of that node or module is
proposed. The original splitting and presentation model remain needed through the
coefficient-trace lemma. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original two-step plan omitted Lean interfaces for the forward ordered square
with proper coincidence and for coefficient trace transport along presentations.
A proved coefficient-first compact projection square already exists, so a new
ringed-topos realization is unnecessary for the first interface. The remaining
trace transport is recorded separately rather than repeating the counit obligation.

The sources read were the current blueprint's
`prop-asd-smooth-base-change.proof.md`, second paragraph, and
`thm-amb-p1-adjunction.proof.md`, its canonical projection/exchange calculation.
The given square and both presentations, positive exponent, zero coefficients,
identity pullback and empty bases were checked. No Noetherian, boundedness or
exceptional adjunction hypothesis is added. Normalized line transport, exchange
pasting and proper coincidence are the remaining coefficient lemma's proof.

## New nodes

`lem-asd-proper-ordered-projection-exchange`: arbitrary-coefficient forward ordered
projection compatibility, including proper coincidence and an arbitrary coefficient
isomorphism. Realized in
`Sheaf.SixFunctors.ProperOrderedProjectionExchange`.

`lem-asd-presented-projective-line-coefficient-trace-exchange`: coefficient trace
naturality on compatible projective-line presentations, before tensoring with an
arbitrary base complex. Realized in
`Sheaf.SixFunctors.ProjectiveLinePresentedTraceExchange`.

The original node's proof and proof dependencies now record the actual Lean
cancellation argument. No existing statement or definition changed, so no consumer
adaptations or change records are required. The general compact projection square
is used as a tool from another unit; it supplies generic projection coherence and
does not replace the projective-line trace step of this unit.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
