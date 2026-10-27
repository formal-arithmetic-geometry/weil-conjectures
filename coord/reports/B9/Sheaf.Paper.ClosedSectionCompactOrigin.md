## What changed

Proved `AlgebraicGeometry.ClosedSectionCompactOrigin.closed_section_compact_origin`
from the canonical compact-support transport data. The parent now obtains its source
normalization from `closedSectionSourceNormalization`, then proves the bounded-below
conclusion and the class-map equation by naturality, cancellation of the source
isomorphisms, and the retained target comparison. The original target statement and
all public names are unchanged.

The data declarations used by the parent were moved to the public support module
`Sheaf.Paper.ClosedSectionCompactOriginData`; the item module publicly imports it, so
its interface is unchanged. The source equation is isolated in
`Sheaf.Paper.ClosedSectionSourceNormalization` as a smaller theorem. The old scratch
attempts and diagnostic probes are outside `lean/` and are not delivered.

## Proved and sorry left

Closed: `AlgebraicGeometry.ClosedSectionCompactOrigin.closed_section_compact_origin`.

Split off: `AlgebraicGeometry.ClosedSectionCompactOrigin.closedSectionSourceNormalization`,
whose proof is `:= by sorry`. This theorem is strictly smaller: it contains only the
source normalization equality and has no target complex, witness isomorphism, bounded
below conclusion, or class maps. No other delivered declaration contains `sorry`.

## No longer needed

The lower-bound proof no longer needs the separate planned resolution nodes
`lem-weil-pbc-extension-by-zero-exact`,
`lem-weil-pbc-module-sheaves-enough-injectives`,
`lem-weil-pbc-dplus-injective-representative`, and
`lem-weil-pbc-kinjective-total-derived`: it transports the existing D+ property instead.
The geometric source-normalization work is retained in the new node, not claimed proved
or pruned. No source-library declaration or module is withdrawn. All original public
imports remain on the item and its data owner.

Removed private proof imports from the item:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion`
  (the original public import remains).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `WeilConjectures.AlgebraicGeometry.ProperBasic`.
- `Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`.
- `Sheaf.AlgebraicGeometry.ProperIdentityOpenSiteComparison`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.ProperOpenCoefficientMate`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.

The parent now imports only the actual source theorem and the compact-support transport
comparison needed for its proof. Its old top-level tool approvals, except the retained
compact-support site comparison, are removed from this parent's route; the mathematical
source step has its own dependencies. This removes no approved dependency that the new
source statement still needs from that statement's own plan.

## Where the brief, the DAG or earlier work was wrong

The original route attempted to construct a compatible proper/open tower and to treat
the standing compactification as the identity model. Compactification existence does
not choose that model. The proof instead uses the canonical transported compositor and
isolates the required source equation as a separate theorem. No target statement was
weakened or disputed.

## New nodes

`lem-pur-closed-section-source-normalization`, realized by
`AlgebraicGeometry.ClosedSectionCompactOrigin.closedSectionSourceNormalization`
in `Sheaf.Paper.ClosedSectionSourceNormalization`. Its statement is the source equation
used by the parent, and its docstring records the mate, proper/exact single-object,
compactification-change, compositor, equality, and identity transport proof.

`def-pur-closed-section-compact-origin-data` is realized in the support module
`Sheaf.Paper.ClosedSectionCompactOriginData`, containing the same
public data declarations previously in the item module; it has no new hole.

The required all-files compiler accepted all three files. This is one hole closed
and one strictly smaller hole added: a decomposition, with zero net hole reduction.
The unpublished closed-single comparison and all experimental definition changes
are retained only outside the delivery; no source-library module is changed.

The module move is recorded in `coord/changes/B9-closed-origin-data-owner.md`.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
