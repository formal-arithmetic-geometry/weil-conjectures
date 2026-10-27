## What changed

Reduced `WeilConjectures.PurUnitTrace.adic_unit_trace_transpose_reductions` using the
completed-unit pullback tower and adic reconstruction declarations. The proof obtains
the base-field core, transports the reconstructed isomorphism to the specified
exceptional operation, transports the uniform finite-Tor bounds to the Tate unit, and
reduces the remaining trace and construction obligations to three smaller public
compatibility statements. Added three proof-only modules, each with its own named
intermediate theorem and DAG node:

- `Sheaf.Paper.AdicUnitTraceTargetNormalization`;
- `Sheaf.Paper.AdicUnitTraceCounitReductions`;
- `Sheaf.Paper.AdicUnitTraceProjectionAssembly`.

The parent imports only these modules and `Sheaf.Paper.SfIntegralConstructibleTriangulated`
for the isomorphism-invariant finite-Tor transport.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurUnitTrace.adic_unit_trace_transpose_reductions`.
The delivery adds these three strictly smaller split-off holes:

- `WeilConjectures.PurUnitTrace.unit_trace_target_normalization` in
  `lem-pur-unit-trace-target-normalization`;
- `WeilConjectures.PurUnitTrace.unit_trace_counit_reductions` in
  `lem-pur-unit-trace-counit-reductions`;
- `WeilConjectures.PurUnitTrace.unit_trace_projection_assembly` in
  `lem-pur-unit-trace-projection-assembly`.

This is a decomposition: one upper hole closed, three lower holes added (net -2
holes). The parent has zero textual holes; the delivered intermediate modules have
three in total. No claim is made that the theorem is axiom-free while those lemmas
remain unproved. No definition contains `sorry`.

The four-module remote compile passed. A stylistic letI warning in the initial parent
proof was corrected to a plain local instance; the corrected parent compiled cleanly
in 19.6 seconds. The final packet is checked again by the delivery tool.

## No longer needed

Removed these private imports from the parent module:

- `Sheaf.Paper.IntegralCompactSupportPrescribedReductions`;
- `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`;
- `Sheaf.Paper.SmoothTrace`;
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`;
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`;
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`;
- `Sheaf.SecSmoothPurity.ReductionCompatibilities`;
- `Sheaf.Paper.CompactSupportProjectionFormula`;
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`;
- `Sheaf.Paper.AdicPuritySourceFiniteness`;
- `Sheaf.Paper.IntegralLineReductionRestriction`;
- `Sheaf.Paper.TensorTraceTranspose`;
- `Sheaf.Paper.SmoothPurityMap`;
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`;
- `Sheaf.Paper.FiniteCoefficientSmoothPurity`;
- `Sheaf.Paper.DerivedNakayama`;
- `Sheaf.SecSmoothPurity.FiniteGeneralRing`;
- `Sheaf.Paper.ProjectionFormulaCoefficientCoherence`.

These remain mathematical prerequisites of the compatibility steps through the new
nodes, or are already public statement prerequisites. No existing node or module is
claimed globally unnecessary and none is withdrawn. The reconstruction dependency is
unneeded for the conditional counit-reduction lemma: its prescribed-lift hypothesis
already supplies the reduction equation. It remains used directly in the parent.
The parent's old `sk-lem-pe-derived-nakayama` tool approval was removed from its
`tool_uses`: Nakayama is now a prerequisite of the projection-assembly node.

## Where the brief, the DAG or earlier work was wrong

The imported plan already separates the conceptual steps but its existing declarations
do not state the bridge between the reconstruction target and the arbitrary specified
RingSystem target. In particular, bare S.finiteRight does not fix the smooth exceptional
counit normalization. The first intermediate states precisely that missing bridge;
the other two expose the separate trace and projection assembly arguments. The parent
statement and all existing definitions are unchanged. The supplied unit record has no
realized node attachment to this auxiliary item; the purity transport route is retained.

## New nodes

`lem-pur-unit-trace-target-normalization` records the counit-preserving comparison
between the actual adic exceptional target and the specified finite-right operation.

`lem-pur-unit-trace-counit-reductions` records the finite reduction identity for the
actual unit trace for every permitted reconstructed lift.

`lem-pur-unit-trace-projection-assembly` records construction of the scalar,
projection, exceptional-transpose, reduction, invertibility, linearity, and cofinal
trace fields from a base trace with normalized reductions.

Each new module has one public statement whose proof is exactly `by sorry`, with a
self-contained source and complete proof in words. Target normalization is a change
of adjoint coordinates independent of purity. Counit reduction is conditional on a
lift and claims no reconstruction. Projection assembly assumes a normalized actual
trace and never reconstructs it. The parent proves the actual reconstruction and
composition connecting these parts, so none of the new statements relabels the
original existential-and-universal theorem.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
