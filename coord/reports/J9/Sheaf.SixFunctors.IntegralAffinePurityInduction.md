## What changed

Filled integralAffinePurity_induction in
Sheaf.SixFunctors.IntegralAffinePurityInduction, preserving its statement.
Private helpers construct the affine-line adjunction from open extension by zero
and integralProjectiveLine_adjunction, compose compact-support adjunctions,
handle scheme isomorphisms, and induct on affineTraceTower. The coordinate
isomorphism then transports the result to the specified Mathlib affine space.
Tate-power, derived-tensor, pullback, and shift comparisons are proved explicitly.
The existing node records these details and their dependencies.
Generic private categorical helpers avoid repeated concrete elaboration.
Sequential elaboration and retaining local let-bindings prevent costly expansion
of the categorical structures during proof cleanup.
The unused-variable, unused-section-variable and unused-tactic lint scans are
disabled locally for this large proof; all Lean kernel and delivery checks remain.
The final complete file compiled without diagnostics in 45.3 seconds;
profiling and diagnostic commands are absent from the delivered module.
Explicit equality transports between the two constructibility predicates avoid
expensive rewriting of the coefficient ring structures.

## Proved and sorry left

Closed the sole original hole:
AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralAffinePurity_induction.
No holes added and no holes left in the delivered module. All private helpers
have complete proof terms. This proof uses the existing stated projective-line
adjunction, localizing compact-support coherence, and Tate-line properties;
their own proof obligations remain with their existing nodes.

## No longer needed

Removed the original proof import
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses: strong monoidality of
the actual derived pullback supplies the required comparison.
The corresponding planned dependency lem-weil-pbc-ringed-topoi-derived-tensor-pullback
is not used directly; its replacement is lem-sfb-derived-pullback-strong-monoidal.
The direct extension-by-zero dependency det-cor-int-compactness-ii-extension-zero
is supplied through the already needed compact-support preservation package;
no separate import or use is required here.
Removed the unused Mathlib.CategoryTheory.Adjunction.CompositionIso import.
No module is withdrawn; the unit's
projective-line and affine-line route is retained. No new split-off module.

## Where the brief, the DAG or earlier work was wrong

No statement repair. The standard chart's quasi-compactness follows directly
from quasi-compactness of its source and quasi-separatedness of its target,
so a separate two-chart computation is unnecessary. The induction is carried
out on the existing coordinate tower and transferred once at the end.

The final delivery remains unpushed. Later compile-service calls failed before
Lean started: stdbuf could not create its temporary directory because the
compile environment reported No space left on device (exit 125).

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
