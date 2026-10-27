## What changed

Proved four of the six remaining theorem bodies in
`Sheaf.Paper.FiniteClopenDerivedDecomposition`, retaining every public declaration,
statement, definition body and public import. Added proved private comparison helpers
and private proof imports. Normalized module gluing supplies the sectionwise module
formulas. The unbounded tensor argument compares the recorded tensor model with the
native K-flat tensor and applies normalized clopen monoidal descent. Scalar extension,
coefficient units and completed restriction use the published normalized comparisons.
The DAG distinguishes these completed arguments from the two outstanding arguments.

## Proved and sorry left

Closed four original holes, all in namespace
`WeilConjectures.PurityFiniteSetting`:

- `finiteClopen_unbounded_decomposition`;
- `finiteClopen_scalar_extension`;
- `finiteClopen_coefficient_units`;
- `finiteClopen_integral_restriction_identification`.

Two original holes remain, under node
`lem-pur-finite-clopen-derived-decomposition`:

- `WeilConjectures.PurityFiniteSetting.finiteClopen_constructible_equivalences`;
- `WeilConjectures.PurityFiniteSetting.finiteClopen_finite_restriction_identification`.

There are two `sorry`s in the item module, zero holes added, zero statements split off,
and no holes in definitions or private declarations. The actual item module compiled in
51.7 seconds. The delivery tool performs the final compilation and axiom checks.

## No longer needed

The proved unbounded comparison uses direct normalized K-flat monoidal descent rather
than normalized ring-isomorphism derived transport. The completed restriction comparison
uses `OpenCompletedRestriction` directly. No dependency needed by either remaining hole
is pruned: their original ring-isomorphism, quotient-system, integral-descent and
field-stage dependencies remain recorded. No module is withdrawn, and the original
public imports are unchanged. The direct tensor-interface import is retained:
removing it changed the elaboration context and increased the real module compilation
from 51.7 to 68.9 seconds, exceeding the limit.

## Where the brief, the DAG or earlier work was wrong

The planned `ClopenRoosIntegralDescent` module imports this item, so it cannot be
imported back here. That observation does not remove the pending constructible argument;
its dependency is retained for a future independent membership interface or other
cycle-free proof. The remaining finite comparison also needs further work on
coefficient-data elaboration: its candidate assembly exceeded the compilation limit.
Neither remaining declaration is counted as proved. No statement or definition is
weakened. The proof-context change record
is `coord/changes/J5-finite-clopen-proof-context.md`. No source-library module is edited.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
