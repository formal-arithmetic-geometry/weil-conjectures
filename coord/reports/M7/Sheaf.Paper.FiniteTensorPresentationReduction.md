## What changed

Reduce `WeilConjectures.PurityFiniteSetting.finiteTensorPositiveReduction_chart`
to the unshifted positive-line chart equation
`WeilConjectures.PurityFiniteSetting.finiteTensorLineChart_reduction`, stated in
the new module `Sheaf.Paper.FiniteTensorLineChartReduction` and imported privately.
The new statement is strictly smaller: it has no diagonal presentation, positive
presentation isomorphism, scalar shift, or shifted coefficient-unit comparison.
It is the ordinary root-basis compatibility in the parent node's Step 8.

A proved private categorical lemma supplies the combination argument. It normalizes
the source and target presentation isomorphisms, cancels the target chart, applies
naturality of the scalar-shift isomorphism to the inverse source chart, and shifts
the unshifted chart equation. The assigned theorem's signature stays verbatim.
The new theorem's docstring and node give its source and complete proof in words,
including degree zero, equal levels, the empty scheme and ramified coefficients.
The unit's route is preserved.

Preserve the existing proof of `finiteTensorStructuralCoherence`. Mark the existing
`finiteTensorTau` wrapper irreducible, with identical body and inferred type, and
set the existing transparency protection options to true. This prevents expensive
native tensor-shift unfolding in its unchanged theorem statement. Its proof is
still a named hole. The change record is
`coord/changes/finite-tensor-tau-transparency.md`.

## Proved and sorry left

This is a decomposition, not a net hole closure. Close the original hole
`WeilConjectures.PurityFiniteSetting.finiteTensorPositiveReduction_chart` by a
complete Lean proof from one strictly smaller new statement. Add one hole:
`WeilConjectures.PurityFiniteSetting.finiteTensorLineChart_reduction`, in
`Sheaf.Paper.FiniteTensorLineChartReduction`, attached to
`lem-pur-finite-tensor-line-chart-reduction`. Thus one original hole is closed,
one is split off, and the net is zero. No definition contains a hole.

Four original holes remain unchanged in the item, all attached to
`lem-pur-finite-tensor-presentation-reduction`:

- `WeilConjectures.PurityFiniteSetting.finiteTensorTwistAdditionCoherence`;
- `WeilConjectures.PurityFiniteSetting.finiteTensorPullbackCoherence`;
- `WeilConjectures.PurityFiniteSetting.finiteTensorTau_reduction`;
- `WeilConjectures.PurityFiniteSetting.finite_tensor_presentation_reduction`.

The private combination lemma is proved for arbitrary categories with integer
shifts. It uses no tensor structure or extra coefficient hypothesis.

## No longer needed

No library module or DAG node is withdrawn, and no original import is removed.
The private symmetry and simultaneous-shift imports remain necessary for the
existing structural-coherence proof. The attempted tau specialization and its
private inverse-shift helpers are outside this delivery; the retained proof does
not add an import of `Sheaf.Paper.FiniteTensorShiftSecond`. The remaining four
assertions retain their source plans and dependencies.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. The earlier attempt's tau proof was
uncompiled; repeated concrete specializations still exceeded the compile limit or
failed on hidden dependent functor arguments. This delivery does not claim that
hole is closed. Even its original statement with a temporary proof hole exceeded
the run cutoff until the tau wrapper was made irreducible; that diagnostic then
compiled in 9.7 seconds.

A combined scratch diagnostic of the positive reduction typechecked in 70 seconds.
Profiling separates 36.6 seconds for checking the new unshifted chart statement
and 27.4 seconds for the assigned chart theorem's proof, with under one second of
tactics. The new statement belongs in its own module by the one-statement-per-new-
module rule; the assigned proof and its generic combination argument stay together.

## New nodes

`lem-pur-finite-tensor-line-chart-reduction`, in
`dag/nodes/sec-smooth-purity/lem-pur-finite-tensor-line-chart-reduction.json`, is the
unshifted root-chart step of the parent's Step 8. Its Lean module is
`Sheaf.Paper.FiniteTensorLineChartReduction`. The parent proof and dependency union
now record the actual presentation-normalization and scalar-shift naturality
argument. The transparency repair is recorded in
`coord/changes/finite-tensor-tau-transparency.md`.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
