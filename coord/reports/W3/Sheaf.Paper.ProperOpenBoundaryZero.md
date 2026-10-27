## What changed

Restored the complete proof of the private theorem
`AlgebraicGeometry.ProEtale.CondensedRing.boundaryVanishing_finite`.
It applies clause (2) of `finiteProperBaseChange` to the chosen pullback
square, pushes the zero restriction forward, and transports zero across
the invertible exchange component.

Added the proved private categorical helper `isZero_source_of_isIso`.
Constructing `asIso` directly at the specialized derived-module category
caused the reported kernel timeout. The helper constructs that isomorphism
in an abstract category and prevents expansion of the derived pullback
comparison during the concrete kernel check. Profiling confirmed that
this complete proof checks with a diagnostic limit of 10,000 heartbeats;
the finite-case kernel check took 0.901 seconds and the complete file
compiled in 38.1 seconds. Diagnostic options were then removed for the
final compile and delivery checks.

The existing public statements, definitions, imports, other proofs and DAG
route are unchanged. No definition repair, consumer adaptation, new
mathematical dependency, or new node is required.

## Proved and sorry left

Closed the one current hole, in the private declaration
`AlgebraicGeometry.ProEtale.CondensedRing.boundaryVanishing_finite`, attached
to `lem-route-boundary-vanishing-finite` and used in step 3 of
`lem-sfb-proper-open-boundary-zero`.

The existing public theorem
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_boundary_zero`
continues to assemble the finite, integral and rational cases.
The new private helper `isZero_source_of_isIso` is fully proved.
Zero holes remain in this module; zero holes added; zero split off.
Imported theorems may themselves still depend on sorry; their holes are
not claimed closed by this delivery.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies are removed.
All existing imports continue to support the unchanged finite, integral,
rational, geometric, constructibility and coefficient-transport proofs.
The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The current module contains one explicit repair hole after its earlier
finite-coefficient proof failed the global kernel check. The inherited
sandbox report claimed a clean proof that no longer matched its source;
that claim has been replaced by verification of this repaired proof.

The timeout is reproduced even with an explicitly supplied `IsIso`
instance passed directly to `asIso`; naming the exchange component alone
is insufficient. Constructing `asIso` in the proved abstract categorical
helper resolves it without altering any definition, signature, or
mathematical assertion. No statement is disputed.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
