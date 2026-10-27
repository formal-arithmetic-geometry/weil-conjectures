## What changed

Proved `WeilConjectures.normalizedIntegralMixedCoherence` in its existing module,
without changing its signature, definitions, or public imports. Added a private
proof import of `Sheaf.Paper.QuotientSystemMixedCoherence`.

The naturality argument adapts the proved lambda/mu naturality calculation in
`IteratedReturnTransportScalarCalculus`. The composition argument adapts the
proved adjunction-mate and reduction calculation in
`PullbackIdentitiesScalarExtension`. Both existing modules depend on this item
through the simultaneous realization interface, so importing them would create a
cycle. Their elementary private calculations are instead proved locally. The
only non-elementary proof input is the existing whole-system `derived_mixed`
coherence equation. Updated the item's node to record this direct proof route.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.normalizedIntegralMixedCoherence`
(`lem-trf-normalized-integral-mixed-coherence`). Both conjuncts are proved.
Zero holes remain in the item; zero holes are added; zero statements are split off.
The imported quotient-system theorem retains its own dependencies.
The final file compiled successfully through `lcompile.py` in 38.3 seconds, with
no warnings or errors. The existing theorem signature is textually unchanged.

## No longer needed

The planned direct proof dependency
`lem-trf-counit-realization-substitution`
(`Sheaf.TraceFormula.CounitRealizationSubstitution`) is unnecessary for this item:
explicit adjunction-counit naturality and cancellation prove the required
coordinate substitution equations without constructing words or proving their
Allowed predicates. Its import was never present in the original item and is
not added. This is removal of one planned proof edge, not withdrawal of that
module or a claim that other users no longer need it. No existing Lean import
was removed. The quotient-system mixed-coherence dependency remains needed.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned word-calculus route is valid but unnecessarily indirect here. The
library already contains a direct proof of the composition equation as the first
conjunct of `pullbackIdentities_scalarExtension`, and an elementary proof of the
naturality equation. Their import dependencies preclude using them by name in
this lower module, but their calculations close this item without new lemmas
with holes. The rework row names an obsolete false-tail import; the current item
and its quarantined copy have the same original single-hole source, with no such
import, so no withdrawal or restoration by an empty module is appropriate.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
