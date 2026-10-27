## What changed

Replaced the whole proof hole in
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothZeroOrientationCoordinates`
by a complete cancellation argument, leaving its signature unchanged. The proof
opens `OrientationNormalized`, installs the supplied `Geometry`, substitutes the
diagonal and section factor identities, and cancels the invertible composite of
the bundle-section adjunct and the normal-section mate. It then cancels
`zeroLineIso.inv` with its hom and uses `Iso.ext`.

Added two independent factor statements in new modules:
`Sheaf.Paper.FiniteEtaleDiagonalCoordinates` compares the diagonal factor with
coefficient-unit coordinates, without an exponent, geometry or orientation;
`Sheaf.Paper.FiniteEtaleSectionIntegration` compares normalized specialization
with rank-zero integration for any closed section of an etale map, without a
smooth orientation or diagonal factor. Both retain the specified geometric maps.
The existing `normalSectionMap_isIso` and `bundleAdjoint_isIso` supply the
cancellation hypotheses; no new invertibility assumption was added.

Read the four original proof dependencies and their Lean signatures. Searched
Mathlib through LeanSearch, LeanFinder, Loogle, msearch grep and local rg. The
existing `finite_smooth_gamma_normalization` has the diagonal identity only for
prime-power coefficients, so it does not specialize to the arbitrary finite ring
in this item. The etale sum right-adjoint base-change theorem supplies a possible
route for the new diagonal lemma, but converting all its exact/left-derived and
adjunction conventions remains part of that lower obligation.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothZeroOrientationCoordinates`
(node `lem-pur-finite-smooth-zero-orientation-coordinates`). No sorry remains in
the item module. This is a decomposition, not a sorry-free proof: one original
hole is replaced by two strictly smaller factor obligations, so the delivery
adds one net hole before any pruning.

Added exactly these two whole-theorem holes:

- `AlgebraicGeometry.Etale.finiteEtaleDiagonalCoordinates`
  (node `lem-pur-finite-etale-diagonal-coordinates`).
- `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteEtaleSectionIntegration`
  (node `lem-pur-finite-etale-section-integration`).

Neither new statement quantifies an `alpha` satisfying `OrientationNormalized`.
The first is the exceptional base-change step alone; the second starts at the
section invariant and computes the remaining two geometric factors. The Lean
proof that combines them uses the original normalization equation and actual
mono cancellation, rather than applying a renamed copy of the item.

All three delivered modules were compiled through `lcompile.py --all`. The
instance-style warning was corrected before final delivery; the delivery tool
runs the final compile and axiom probes. No definitions were changed.

## No longer needed

No existing imports or modules are removed; no global pruning is claimed.
The original direct dependency on `def-amb-vector-integration` is now needed by
the new section lemma. `lem-pur-etale-support-map-compatibility` is needed by
both new geometric obligations. `prop-asd-smooth-base-change` is not applied
directly by the assembly proof; its invertibility and mate machinery remains
used through the existing normal-section theorem and the lower factor proofs.
`lem-trf-finite-ring-section-deformation` remains a direct dependency through
`bundleAdjoint_isIso`. The DAG now records these actual dependencies and the
normal-section invertibility theorem. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The former node proof
compressed two specific map-coordinate identities into prose. The stated
support-exchange, deformation uniqueness and integration declarations do not
immediately assert those arbitrary-finite-ring identities in these coordinates.
The two new statements expose those distinct steps instead of splitting off the
whole supplied-orientation equality again.

Edge cases checked at the statement level: the identity etale map gives an
identity section and empty complementary clopen piece; non-surjective etale maps
and disconnected schemes keep the complementary piece and require no global
sheet decomposition; empty schemes and the zero coefficient ring give the same
map equalities in zero categories. The equality `hd : d = 0` is explicit, so no
positive-rank specialization or integration assertion is being made.

## New nodes

`lem-pur-finite-etale-diagonal-coordinates` records the first factor of the
three-factor formula in the latest blueprint orientation proof. The proof plan
uses graph/homotopy uniqueness, compatibility of support exchange, adjoint
triangles, and restriction by the diagonal. Its public Lean theorem lives alone
in `FiniteEtaleDiagonalCoordinates.lean`.

`lem-pur-finite-etale-section-integration` records the second and third factors
for a general closed etale section. The proof plan computes the Rees algebra on
its two clopen pieces, identifies the normalized comparison by uniqueness, and
uses the identity rank-zero trace and cone/bundle compatibility. Its public Lean
theorem lives alone in `FiniteEtaleSectionIntegration.lean`. The blueprint search
found no existing node for either precise factor identity. No change record is
needed: existing interfaces, definitions and public imports are unchanged.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
