## What changed

Proved both existing theorems in `Sheaf.Paper.FrobeniusCompactSupportExchange`, with
all public signatures, definition bodies, existing docstrings and visibility preserved.
Four private proved helpers assemble the intrinsic pullback equivalences, finite
proper/open exchange, integral isomorphism detection by complete cones and the canonical
Roos triangle, and the integral exchange. Rational localization and
the common-stage inclusion preserve their inverse arrows, and the supplied arrow
isomorphisms identify the specified components. Full-subcategory reflection and
componentwise invertibility finish both existing natural transformations.

The six-step route remains: geometry, finite proper mate, open factor, supplied
reduction comparison, complete cone, and coefficient passage. The node now records
the exact intrinsic-coordinate APIs and scalar-reduction exactness actually used.
The intrinsic equivalence is assembled directly from existing composition/identity
isomorphisms instead of transporting through tensor-pullback coordinates.

Validation: the item is checked through lcompile.py. The delivery gate performs the
final compile and per-declaration axiom/sorry probe. No other module is
adapted, no new public statement or definition is introduced, and no target changes.

## Proved and sorry left

Closed 2 of 2 existing holes:

- `WeilConjectures.PodFrobeniusExchange.rational_isIso`.
- `WeilConjectures.PodFrobeniusExchange.commonStage_isIso`.

Added holes: 0. Remaining holes in the delivered module: 0. Split-off statements: 0.
Both statements retain node `lem-pod-weil-frobenius-compact-support-exchange`.
Imported declarations may retain their own existing proof obligations; none is
restated or replaced here. The private helpers are all completely proved.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.SfRationalizationKaroubi`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.AlgebraicGeometry.IsomorphismDerivedPullbackEquivalence`.
- `Sheaf.Paper.CompactificationCoherence`.

Pruned direct proof dependencies (and their obsolete top-level tool approvals where
present):

- `lem-weil-isomorphism-derived-pullback-equivalence`: its tensor-pullback coordinate
  bridge is unnecessary; intrinsic composition and identity supply the equivalence.
- `lem-cbc-proetale-extension-zero-base-change`: the finite exchange already contains
  the canonical intrinsic open-square isomorphism, from `lem-trf-open-square-exchange`.
- `prop-compactification-coherence-detailed`: the item fixes a compactification and
  its base change; no independence comparison is required to prove invertibility.
- `lem-pur-derived-change-of-rings`: its generic construction need not be used again;
  the actual specialized reduction exposes its exactness in
  `def-weil-integral-derived-reduction` and
  `lem-weil-derived-scalar-extension-restriction-adjunction`.

`DerivedCompleteOnSlices` is unnecessary here: the supplied integral category uses
`IsSfDerivedComplete` and its literal Roos triangle. The derived-completeness node
remains as the mathematical dependency; no slice/global comparison is asserted.
Other removed imports merely duplicated declarations available through retained
statement imports. No public import is removed. These are direct dependency prunings;
this report does not claim that the modules are globally unreachable from targets.

## Where the brief, the DAG or earlier work was wrong

The mathematical six-step plan was sound. Its chosen generic finite-pullback and
open-exchange interfaces use different coefficient presentations from sfExchangeShriek.
The intrinsic composition/identity API and the open isomorphism already embedded in
that definition give the same argument directly. Likewise exactness of the actual
scalar reduction is already part of scalarReductionDerivedExistence. The node has
been updated to those declarations, rather than adding redundant bridge obligations.

Edge cases remain covered: zero or empty operation domains are handled by the universal
component argument; no nonempty scheme, separated base, stable lattice or faithfulness
of all reductions is assumed. Zero detection uses completeness of the cone, not of
arbitrary objects. Every positive exponent n+1 is used. At a literal common coefficient
stage the inclusion functor itself carries both inverse identities.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
