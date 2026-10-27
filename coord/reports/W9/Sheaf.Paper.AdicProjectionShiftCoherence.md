## What changed

Decomposed `WeilConjectures.adicProjectionShiftCoherence` into three independent,
strictly smaller obligations. Its complete original signature is unchanged. The parent
assembles the completed projection theorem at the chosen, proper-only and open-only
compactifications. It constructs the canonical exceptional shift, proves counit-only
uniqueness by the adjunction Hom bijection, derives the trace square by cancelling the
invertible projection, and applies the arbitrary-map transpose square.

Moved the existing eleven definitions/instance declarations verbatim to
`Sheaf.Paper.AdicProjectionShiftData`, publicly re-exported from the original module.
The existing definition-owner node follows that move. Every original public import
is retained in the data module, so consumers see the identical public interface.
The change record is `coord/changes/W9-adic-projection-shift-data.md`.

All work is under the sandbox. No source-library declaration or target was changed.
The main theorem signature and the moved declaration block were compared byte for byte
with the shared source. New statements were checked on zero objects and zero trace,
identity/proper/open compactifications, odd first degrees, and arbitrary (including zero)
source comparisons; none adds a concentration or invertibility requirement on the trace.

## Proved and sorry left

Closed the original hole of `WeilConjectures.adicProjectionShiftCoherence` by a
compiling assembly. This is a decomposition, not a net proof: one hole closed,
three holes added. The private `counit_shift_unique` helper is proved completely.
No sorry remains in the item module or in any definition.

Remaining named public theorem holes:

- `WeilConjectures.adicCompletedProjectionShift`, node
  `lem-pur-adic-completed-projection-shift`: completion-domain/invertibility witnesses
  and the completed projection square; no trace or exceptional adjunction conclusion.
- `WeilConjectures.adicTraceTensorShift`, node `lem-pur-adic-trace-tensor-shift`:
  the ordinary-to-completed tensor/unitor normalization for any trace; no projection
  square or projection invertibility assertion.
- `WeilConjectures.adicExceptionalTransposeShift`, node
  `lem-pur-adic-exceptional-transpose-shift`: transpose of an arbitrary assumed ambient
  shift square; no projection or trace construction, closure or invertibility assertion.

Each new theorem has exactly `:= by sorry`, its own module and DAG node, source and
complete proof in words. The split-off obligations retain the source route.

## No longer needed

Removed four private imports from the original item: `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`, and
`Sheaf.SixFunctors.IntegralRealizationShiftCoherence`. The parent no longer invokes
these directly; the completed-projection obligation retains the actual strict-system
and realization route. No mathematical dependency module is claimed globally pruned.
All original public imports are retained through the data module.

The parent's former direct DAG dependencies now belong to the completed-projection
step: `def-exchange-projection`, `lem-weil-pbc-ringed-projection-mate-exact`,
`lem-pur-open-system-tensor-shift`, `lem-pur-strict-compactification-projection-shift`,
`lem-pur-system-level-projection-formula-coherence`,
`lem-sf-integral-compactification-system-realization`,
`def-weil-integral-rational-qbar-compact-support`,
`lem-pur-integral-realization-shift-coherence`, and `fix-prop-projection-formula`.
The parent directly retains the Mathlib adjunction-shift node and the three new steps.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic realization theorem supplies a `Realizations` package and formal expression
squares, not the specialized square for arbitrary supplied `d`, `b`, and the displayed
completion inverses. Its closure and normalization specialization is genuine remaining
work, isolated in `adicCompletedProjectionShift` rather than inferred from faithful finite
evaluations. The tensor shift data do not directly provide a `CommShift` instance for the
completion-normalized trace tensor/unitor composite, hence its separate obligation.

A direct proof of the exceptional transpose exposed coercion/derived-category-instance
mismatches between `scalarReductionSource` and the realized completed-ring presentation.
The remaining theorem states just that ambient-to-full-subcategory normalization step,
with arbitrary source morphisms and maps. The parent performs the projection cancellation
and counit-only uniqueness itself; none of the new statements repackages the whole item.

## New nodes

`lem-pur-adic-completed-projection-shift` records the specialization of strict-system
projection and integral realization coherence to the actual completed projection map,
including closure and invertibility. It retains the original first three proof steps.

`lem-pur-adic-trace-tensor-shift` records the independent signed tensor/unitor calculation,
with no finite-Tor assumption on the first input and no projection-formula conclusion.

`lem-pur-adic-exceptional-transpose-shift` records the full-subcategory/ambient realization
of the generic adjunction shift calculation, for arbitrary maps satisfying an ambient square.

Definition ownership moves to `AdicProjectionShiftData` without new definitions. The change
record is `coord/changes/W9-adic-projection-shift-data.md`. LeanSearch, Loogle/LeanFinder and
grep searches ran through msearch; blueprint searches for projection shift, trace shift,
adjunction shift and transpose shift found no exact blueprint duplicates.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
