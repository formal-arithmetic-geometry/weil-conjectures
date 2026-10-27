## What changed

Proved `AlgebraicGeometry.strictEtaleExceptionalTransport_identity` in
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`. Private helpers normalize the ordinary
identity on tensor units, prove successor compatibility by faithful forgetting,
descend through the derived localization, identify the geometric inverse-image
squares, and transpose the open, proper, and exceptional squares. All private
helpers are proved. The identity proof uses no faithfulness of derived evaluation.

Replaced the existing Brown evaluation-mate calculation by a general private
counit-mate lemma and made its transition identification explicit. Local
irreducibility annotations prevent unnecessary expansion of coefficient objects
while checking the transport interfaces. Public declarations and imports retain
their statements and definitions. The node's scalar-coherence step now records the
identity proof actually written.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.strictEtaleExceptionalTransport_identity`.
Added zero holes; split off zero statements.

Three original holes remain, all attached to
`lem-pur-etale-coefficient-system-adjoint`:
`AlgebraicGeometry.etaleCoefficientSystemAdjoint_scalar`,
`AlgebraicGeometry.etaleCoefficientSystemAdjoint_cofinal`, and
`AlgebraicGeometry.strictEtaleExceptionalTransport_comp`.
The existing `etaleCoefficientSystemAdjoint` proof is preserved.

## No longer needed

None. The identity proof needs no additional proof-dependency imports. The scalar,
cofinal, and composition assertions still need the dependencies in the node's
remaining plan, so no modules or dependencies are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior attempt stopped without a compiling reduction. The identity assertion
can be proved directly from the normalized interfaces already in this module and
Mathlib's localization and mate APIs. No new mathematical statement is needed.

The compile server briefly reported a temporary-directory disk-space error;
subsequent fresh compiles resumed successfully. Diagnostic drafts and profiler
settings remain in `scratchpad/` and are not part of the delivery.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
