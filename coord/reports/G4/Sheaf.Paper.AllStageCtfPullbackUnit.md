## What changed

Proved `WeilConjectures.AllStageCtfPullback.preserves_ctf_and_unit` in
`Sheaf.Paper.AllStageCtfPullbackUnit`, with its public signature unchanged.
The finite clauses apply the existing proved `sf_pullback_torAmplitude`, then
transport constructibility and the supplied interval through
`openSquareDerivedPullbackModel`. A private, proved helper transports Tor
amplitude along an isomorphism by composing the representative isomorphisms.

For integral coefficients, `integralOperations_preserve_constructible` supplies
constructibility and invertibility of the specified comparison for every good
representative. A private, proved helper obtains a flat-term K-flat representative
from derived localization and the existing resolution theorem. At each level the
proof composes the actual comparison with `integralFinitePullbackModel`, exact
pullback's derived factorization, `coefficientFiniteReductionModel`, and the
intrinsic pullback comparison. This identifies reduction after integral pullback
with finite pullback after reduction. The finite result transfers the same
endpoints `a,b` at every level. Unpacking the finite and integral predicates gives
the two full-subcategory preservation assertions.

The existing `residueInvertible`, `rationalUnit` and `commonUnit` definitions are
unchanged. The finite and completed integral units remain publicly imported from
`ConstantGeometricStalkUnit`; the field units still apply the specified
localization and same-stage inclusion to that actual integral unit.

Added only private proof imports for tensor flatness comparison, finite pullback
coordinates, isomorphism closure, the integral finite-pullback presentation and
integral constructibility preservation. Updated the existing node's proof,
proof dependencies and proof origin to describe this argument, and removed its
obsolete tool-use entries. No public import, target, definition, statement,
source-library file or consumer was changed; no change record is required.

## Proved and sorry left

Closed one hole: `WeilConjectures.AllStageCtfPullback.preserves_ctf_and_unit`
(node `lem-pur-all-stage-ctf-pullback-unit`). Added zero holes; zero holes remain
in the delivered module. Both new private helpers are fully proved. No new
statement is split off.

The proof reuses existing dependency declarations; this report does not claim to
close holes in those dependencies. Single-file `lcompile.py` passed with exit code 0 in 12.8 seconds, without
warnings. The delivery tool also runs its compile, axiom probe and preflight.

## No longer needed

Removed these direct private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.ConstantScalarStrictUnit`
- `Sheaf.SixFunctors.CompletedCoefficientFreeResolution`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`

Their former direct proof nodes are no longer needed as direct dependencies:
`prop-weil-pbc-proetale-constant-ring-map`,
`prop-weil-pbc-proetale-constant-exact`,
`lem-weil-constant-scalar-strict-unit`,
`lem-sf-completed-coefficient-free-resolution`,
`lem-pur-integral-operations-well-defined`,
`lem-pur-integral-operations-scalar-extension`, and
`lem-weil-constant-coefficient-objects-constructible`.
The matching obsolete entries were removed from `tool_uses`, preserving the
remaining order. Existing units and derived-operation definitions already
encapsulate these constructions. Most remain transitive imports.

A source-import closure comparison shows that
`Sheaf.SixFunctors.CompletedCoefficientFreeResolution` and
`Sheaf.Paper.CompletedFreeCellOrdinaryLimit` leave this item's import closure.
Other consumers may still need these modules; none is withdrawn or deleted.
The unit's recorded route is preserved and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The old proof plan spelled
out constructions of units which are already available in the publicly imported
`ConstantGeometricStalkUnit` interface. The proof now cites and reuses those
constructions. For the preservation theorem, the extra work is the explicit
change between its two finite pullback presentations and the integral reduction
comparison; the packet supplies both compositions in Lean.

The rework row records an earlier transitive projective-line import failure.
The assigned module is present in the current shared source; this packet starts
from that live restored source and preserves its Lean attachment. It does not
withdraw the module or modify the quarantined archive. There is no current
item-specific numbered return in `coord/returns/G4.md`.

Edge cases are preserved by the proof: no nonemptiness or separatedness of the
base schemes is added, n=0 is exponent one, and the same ordered interval from
the input is retained. Identity maps and zero complexes use the same argument.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
