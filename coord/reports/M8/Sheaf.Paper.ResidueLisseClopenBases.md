## What changed

Replaced the proof hole of `WeilConjectures.residue_lisse_clopen_bases` by an assembly
from the existing simultaneous clopen localization theorem. Its public statement
and the actual `topCellIntegralFree` and `topCellResidueFree` objects are unchanged.

The proof obtains finite local residue models from constructibility, geometric
stalk pullback comparison, and the pro-etale finite-model theorem. Exact derived
restriction identifies cohomology. Finite biproducts identify the integral free
objects with the products covered by the existing projectivity conclusion. The
original Tor interval is retained on every pro-etale object using exact pullback
and the field-coefficient tensor calculation.

Added `ClopenCompletePullbackComparison` and `ClopenResidueFreeRestriction` as
separate proved comparison modules. The first identifies the coefficient datum
with `OpenCompletedRestriction` by constant-section and projection normalization,
then applies the existing clopen completion-restriction theorem and inverts the
completion unit. The second transports a finite biproduct of coefficient units
through the concrete slice functor. These are individual comparison steps, with
no partition, constructibility, projectivity or Tor conclusion in their statements.

Only the assigned module, these two new modules, their nodes and the assigned
node's proof route are changed. No existing shared interface or source-library
file is changed.

Validation: all three delivered modules compile through `lcompile.py` without
warnings. The final assigned-module compile took 6.3 seconds; the separate
comparison compiles took 15.5 and 9.5 seconds.

## Proved and sorry left

Closed the one original hole, `WeilConjectures.residue_lisse_clopen_bases`.

Added zero holes. Both new declarations are proved:

- `WeilConjectures.sf_clopen_complete_pullback_comparison`
  (`lem-sf-clopen-complete-pullback-comparison`).
- `WeilConjectures.sf_clopen_residue_free_restriction`
  (`lem-sf-clopen-residue-free-restriction`).

No `sorry` remains in the delivered Lean files. This is a proof from existing
library declarations; in particular the existing
`WeilConjectures.clopenIntegralCompletionRestriction` remains an imported proof
obligation. It has not been restated or copied as a new hole.

## No longer needed

The original proof-only dependency
`lem-weil-pbc-finite-locally-constant-module-values` is not used: it concerns the
etale finite-values interface. Pro-etale geometric stalk comparison and
`ProEtale.finiteModels_over` give the required finite local module models directly.
The assigned node's proof dependencies now name these actual declarations.

No original public imports were removed, and no module is withdrawn. The
weakly-etale localization dependency is still needed in the residue comparison.
The localization package's Tor-compatibility field is not used by the assembly;
its source theorem and dependencies remain intact. The exact field Tor argument
supplies the precise full-site Tor statement needed here instead.

## Where the brief, the DAG or earlier work was wrong

The original plan did not state the comparisons between its slice constant models,
its normalized ordinary restriction, and the specific completed pullback functor.
The two comparison modules make those steps explicit and prove them from existing
interfaces. The old finite-values dependency is an etale theorem, whereas this
statement uses the small pro-etale site. No statement was found false and no target
or definition was changed.

The unit `sk-rem-sf-pf-done` has no realized statement/proof-step entries that this
route bypasses. The residue Tor interval is shared across all components and all
their pro-etale objects; the finite rank function is extended by zero outside it.
The comparison arguments allow empty opens and rank zero.

## New nodes

`lem-sf-clopen-complete-pullback-comparison` records the normalized ordinary versus
completed restriction comparison on an arbitrary complete input. It is proved
using the existing completion-restriction theorem, uniqueness of normalized
coefficient data, and the canonical completion-unit criterion.

`lem-sf-clopen-residue-free-restriction` records transport of a supplied rank-r
slice constant model to the actual rank-r free residue sheaf. It is proved by
finite biproducts, the constant-unit comparison, and the concrete slice functor.

Both nodes retain the assigned chapter and unit and cite their source proof step.
No change record is required: no existing statement or definition was changed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
