## What changed

Replaced the remaining proof of
AlgebraicGeometry.ProEtale.SpPurityReduction.purity_conjugates_tower_reduction
by a complete assembly from two proper transport steps. The proof constructs
normalized finite orientations using finiteGeneralRingOrientation; proves
sourceComparison invertible by induction through the ordered line tensor word;
uses smooth_tensor_duality for ordinary finite gamma invertibility; defines each
gamma by the inverse source comparison and the specified finite arrow; pastes the
source-reduction and finite-purity squares; and cancels gamma to derive conjugacy.
The actual exceptional reduction formula is exactly lv.reduction.

Moved pullbackTower, sourceWord, sourceComparison and targetComparison verbatim to
PurityTowerReductionComparisons and publicly re-exported them. Their signatures
and bodies were compared mechanically and are identical; their docstrings now
point to the new definition-owner node. This prevents an import
cycle when stating the two transport steps. No target or mathematical statement
changed. Existing tor_cohomology and pullbackTower_bounds proofs are unchanged.

Change record: coord/changes/B3-purity-reduction-comparison-ownership.md.

## Proved and sorry left

Original holes: 1. Closed in the parent module:
AlgebraicGeometry.ProEtale.SpPurityReduction.purity_conjugates_tower_reduction
(node lem-sp-purity-conjugates-tower-reduction), from two strictly smaller steps.
This is a decomposition, not a net proof: 1 hole closed, 2 holes added, net -1.
The parent module has zero remaining sorry.

Holes added, and all holes left in this packet:

- AlgebraicGeometry.ProEtale.SpPurityReduction.pullback_reduction_transport
  (lem-sp-purity-pullback-reduction-transport), in
  Sheaf.Paper.PurityPullbackReductionTransport: only actual input and twisted
  pullback reduction transport, with no exceptional purity or gamma construction.
- AlgebraicGeometry.ProEtale.SpPurityReduction.finite_purity_reduction_transport
  (lem-sp-purity-finite-reduction-transport), in
  Sheaf.Paper.PurityFiniteReductionTransport: the finite coefficient/naturality
  square in exceptional coordinates, conditional on supplied normalized finite
  orientations and actual input arrow, with no tower gamma or source reduction.

Each is a public named theorem with exactly `by sorry`, a source and complete
natural-language proof, and its own new module and DAG node. Neither restates the
parent: their combination still requires the proved isomorphism construction,
normalization equation, exceptional reduction formula, square pasting and inverse
cancellation. Edge cases checked in the statements: m=n, d=0, K=0, empty schemes,
zero input reductions, ramified E and nonflat coefficient quotients. No arbitrary
data is defined by choosing an unproved existence witness; only normalized
orientations determined by their diagonal/deformation equation are selected.

## No longer needed

Direct public imports removed from the parent:
Sheaf.Paper.SmoothPurityTowerGamma (replaced by the comparison-definition owner,
which publicly re-exports it), Sheaf.Paper.FiniteSmoothCoefficientArrows (available
through that owner), Sheaf.SecSmoothPurity.ReductionCompatibilities,
Sheaf.SecSmoothPurity.FiniteGeneralRing, Sheaf.Paper.DerivedPullbackTensorIso and
Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted. The parent proof instead
privately imports FiniteGeneralRingOrientation, SmoothTensorDuality and the two
transport steps. None of these public-import removals changes any existing
consumer: there are zero current importers, and the theorem signatures remain
identical.

The parent proof no longer directly uses lem-pur-derived-pullback-tensor-iso,
det-sp-scalar-extension-functor, det-sp-coefficient-towers-abelian,
det-sp-reduction-compatibilities, det-sp-finite-general-ring,
lem-sp-finite-orientation-reduction or def-pur-smooth-purity-map as proof steps.
The first six remain mathematical dependencies of the new transport steps, and
are not globally withdrawn. No module is claimed globally pruned. The unused
parent tool approvals for those proof steps were removed without adding approvals.
The unit route, finite orientation normalization, ordinary tensor-transpose gamma,
and actual reduction equations are preserved; tower_gamma is never used.

## Where the brief, the DAG or earlier work was wrong

The parent initially had one sorry, not two: its bounds theorem had already been
proved. The plan's elementary source-reduction step hides transport through the
retained ordinary origins, site/scalar comparison, realization counit and ordered
Tate-line word; no existing declaration states that combined actual reduction
formula. ReductionCompatibilities_purity uses a common exponent and its fixed
pro-etale realization, while this consumer uses different positive exponents and
the supplied counit-normalized right-adjoint realizations. The two transport
lemmas isolate these gaps without strengthening assumptions or changing arrows.

## New nodes

- def-sp-purity-reduction-comparisons: owns the four unchanged canonical word and
  comparison definitions; no holes or new mathematical construction.
- lem-sp-purity-pullback-reduction-transport: transports the actual input and
  pullback/tensor reduction; source is gamma proof (3), first formula.
- lem-sp-purity-finite-reduction-transport: finite coefficient compatibility and
  naturality in the specified output coordinates; source is gamma proof (3),
  coefficient square and its pasting with the actual input reduction.

Validation performed during development: all four moved definitions have identical
signatures and bodies; both original theorem signatures are identical; all new
node dependencies exist and proof_deps equal the union of proof-step uses; no
cycle passes through a new or changed node; every Lean line is at most 100 columns.

All four modules compile through lcompile.py. The parent compiled without warnings
in 49.6 seconds. Its coefficient comparison uses equation recursion and an explicit
packaged-word IsIso instance, avoiding repeated dependent-recursion conversion.
No profiler or trace option remains.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
