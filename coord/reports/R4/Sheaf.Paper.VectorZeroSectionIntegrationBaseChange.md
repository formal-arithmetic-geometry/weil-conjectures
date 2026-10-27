## What changed

Restored the assigned quarantined module from its archive, preserving its theorem
signature, public imports, and Lean attachment. Replaced its hole by an explicit
composition of two argument steps: transpose a compact-support trace square under
the actual Brown adjunctions, then pull that square along the new zero section.
Two proved private categorical lemmas perform the mate counit calculation and the
restriction calculation. Adjunction naturality identifies the normalized adjuncts
with the existing definition of vectorBetaInverse.

Added proof-only imports of Sheaf.Paper.VectorNormalizedTraceCartesian and
Sheaf.Paper.OrderedTatePullbackSquare. Each new module contains one named remaining
theorem, with a source, a complete proof in words, and its own node. Updated the
item's proof route to agree with these imports. No existing definition, statement,
attribute, or public import changed. No change record is necessary.

Validation: lcompile.py --all compiled both new modules and the restored item
successfully (exit code 0). The overlay DAG check found no dependency cycle through
the assigned item.

## Proved and sorry left

Closed the original hole in
WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_zero_section_integration_baseChange
(lem-pur-vector-zero-section-integration-base-change). The assigned module has
zero remaining sorry bodies. Both private helper proofs are complete.

Added two holes:

- AlgebraicGeometry.Etale.orderedTatePullbackSquare,
  node lem-pur-ordered-tate-pullback-square, in
  Sheaf.Paper.OrderedTatePullbackSquare. This is solely composition of the finite
  Tate coefficient comparisons around an arbitrary commutative square; it contains
  neither integration nor exceptional inverse image.
- WeilConjectures.PurityFiniteSetting.OrientationRefinement.vector_normalized_trace_cartesian,
  node lem-pur-vector-normalized-trace-cartesian, in
  Sheaf.Paper.VectorNormalizedTraceCartesian. This is the compact-support trace
  equation on the total space, before transposition or restriction to a section.
  Its proof plan uses the already stated general-modulus normalized family and
  its base-change equation, together with the projection-unit calculation.

This is a decomposition: one original hole closed and two added, not a complete
proof of the lower obligations or a net reduction in holes. The combination proof
performs the transposition, compositor naturality, source-factor cancellation,
and identification with vectorBetaInverse in Lean.

## No longer needed

No existing module is withdrawn and no original public import is removed.
The item retains its original VectorBundleFiniteTypeFrames import for the
smooth-dimension witness in its statement and proof.

The original direct proof dependencies cor-pur-vector-bundle-purity,
det-prop-sfb-cartesian-coefficients-twists, lem-asd-etale-finite-twist-pullback,
and lem-weil-pbc-mate-pasting are replaced by the two narrower steps and the actual
Mathlib mate-counit and adjunct-counit leaves. Vector-bundle purity remains on the
route through its normalized-family declarations and the unchanged data import.
The finite twist pullback theorem remains below the coefficient step. The
pro-etale CartesianCoefficientTwists theorem is unnecessary for this ordinary-etale
calculation, though its existing public import in the shared data module remains.
The combination uses a single mate counit identity and does not require a mate
pasting theorem. None of these observations asserts whole-library pruning.

## Where the brief, the DAG or earlier work was wrong

The item was absent from lean/ because it was quarantined; its archive and rework
entry were preserved and used, rather than treating the absence as withdrawal.
The source and original argument are mathematically consistent, including
nonlinear zero-preserving Cartesian maps, rank zero, and empty schemes.

The published VectorBundlePurity conclusion is specialized to ringChar, while the
item fixes the diagonal exponent. The general-modulus vectorBundleNormalized and
vectorIntegrationCounit_baseChange declarations supply the appropriate route;
the remaining extraction of their coefficient-unit trace equation is isolated in
the new compact-support theorem. No downstream smooth diagonal orientation or
Thom theorem is required. An overlay dependency check finds no return path from
either new node to the assigned item.

## New nodes

lem-pur-ordered-tate-pullback-square records the coefficient-only square equation
for normalized ordered Tate tensors. Its proof is induction on the ordered tensor
power, with constant-unit composition in degree zero and normalized roots, pure
tensor generators, exact realization and shift composition for the line factor.
Searches found generic pullback tools but no matching Mathlib statement. The
statement includes arbitrary commutative squares, empty schemes, rank zero, and
the zero coefficient ring.

lem-pur-vector-normalized-trace-cartesian records the actual compact-support
integration square with the Tate coefficient moved to the total space. Its proof
starts with the existing independently normalized gamma family at the diagonal
exponent, takes the unit component of the existing base-change equation, uses
projection right-unitality and mate counit identities, and restores the specified
Tate comparisons. It is a genuine step before the adjunction and restriction
operations proved in the item. Searches found the canonical pullback trace law
and normalized-family law in the project, but no direct equation with these
unit and total-space coefficient coordinates in Mathlib or the project.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
