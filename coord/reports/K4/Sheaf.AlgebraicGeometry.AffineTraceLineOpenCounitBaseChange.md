## What changed

Filled `AlgebraicGeometry.Etale.affineTraceLineExchange_openCounit` in
`Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange`, with its statement unchanged.
Private, proved helpers identify the existing unbounded derived operations with the
compact-support formalism: composition and identity comparisons, open base change,
proper/open exchange, and the actual common-refinement comparison. Refinement compatibility
then identifies the exchange with the formula on the standard projective compactification.
The final equality is the existing open-counit base-change identity followed by naturality
of proper direct-image exchange. All added proof imports are private.

The square and exact/left-derived pullback comparisons are checked explicitly. No data
construction, public definition, target, or consumer interface changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.affineTraceLineExchange_openCounit`.
Added zero holes, split off zero obligations, and left zero `sorry` declarations in this
module. Every private helper is proved.

Validation: the full file compiled in 30.9 seconds, and `#print axioms` for the assigned
theorem reported exactly `propext`, `Classical.choice`, and `Quot.sound`. New import
directions were checked for cycles. Redundant imports were removed afterward; the
delivery compile checks the final import list.

## No longer needed

Removed the original direct proof imports:

- `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`;
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`;
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`.

Also removed redundant exploratory imports of
`WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange` (already public through
`AffineTraceConstruction`) and
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence` (already public through
`ClopenTransfer`).

The bounded-below packaging in `cor-cbc-derived-extension-zero-base-change` is not used:
the argument works directly with unbounded derived open base change. The source sheaf
base-change result remains used through the derived construction. No source declaration
or module is withdrawn; these dependencies may remain needed elsewhere.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original plan is valid, but its
bounded-below extension-zero interface is unnecessary for this unbounded statement.
The common-refinement cancellation is implemented using the existing abstract formalism's
refinement compatibility, after proving its exact identification with the concrete
unbounded comparison. Private categorical helpers follow existing source proofs and add
no new geometric assumptions. The unit route is retained.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
