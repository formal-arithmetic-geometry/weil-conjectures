## What changed

Proved `vectorCoefficient_plus` in `Sheaf.Paper.ProEtaleVectorIntegration` using
`rightTower_plus`, affine coefficient descent, and the affine tower zero section.
Added a private exact-pullback boundedness helper and private proof imports of
`UpperStarIdCoherence`, ordinary vector integration, and normalized Tate-transport
and projective-line datum uniqueness.

Reduced `existsUniqueVectorIntegration` to comparison of the independent ordered
affine trace. The proof transports ordinary vector integration by the original
`vectorSite` and proves the normalization equivalence from canonical pullback
naturality. Comparison is bijective on maps to the bounded-below constant target;
ordinary degree-zero gluing uniqueness proves uniqueness upstairs. The original
public statements and definitions are unchanged.

`OrderedIntegrationComparison` proves the coordinate induction from the separate
one-step `LineCounitComparison` statement. Its source is the actual recursively
defined proper/open comparison, and its counits remain the independently defined
supported-Kummer counits. Both comparison statements have matching DAG nodes.

Validation: the full dependency set compiled through `OrderedIntegrationComparison`;
the final main-module check then compiled successfully in 30.7 seconds with no
warnings. Delivery preflight validates the complete packet together.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorCoefficient_plus`.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.existsUniqueVectorIntegration`
  (reduced using the separately stated line-counit comparison).

New remaining hole:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.lineCounit_comparison`, node
  `lem-pur-line-counit-comparison`, in `Sheaf.Paper.LineCounitComparison`.
  This is strictly the one-coordinate map-comparison argument; it contains no
  vector bundle, frames, descent, or gluing. Its docstring and node give the
  projective Chern, proper projection, and open counit proof.

No holes remain in the item module. Two original holes closed, one hole added;
this is one proved boundedness result and one decomposition, with net one hole
closed. No definition contains `sorry` and no arbitrary existence witness is
used to define data.

## No longer needed

No existing public import or module is removed. The boundedness proof does not
need a new derived tensor-amplitude lemma: the existing `rightTower_plus` and
zero-section retraction suffice. The gluing proof reuses ordinary
`existsUnique_vectorIntegrationGluing`; it does not use
`Sheaf.Paper.DegreeZeroDerivedMapGluing` or
`Sheaf.Paper.VectorFrameIntegrationSiteDescent`, and does not duplicate their
pro-etale descent argument.

The all-Noetherian comparison reduction does not use
`Sheaf.Paper.AffineTowerIntegrationSiteTransport` or
`Sheaf.Paper.P1KummerTraceSiteTransport`, whose current theorems impose finite-type
over-field hypotheses. No claim of globally pruning these modules is made:
other consumers and unfinished parents still need them. No statement dependency
of an existing public signature has been deleted.

## Where the brief, the DAG or earlier work was wrong

The item node initially had no numbered proof steps. Its docstring described the
projective/open comparison and gluing plan, but the available acyclic packaged
transport theorems apply only to finite-type schemes over a field. The item
allows arbitrary Noetherian bases. The new one-step comparison records the
specific generality actually needed; no target or existing statement was
weakened. The module `VectorIntegrationSiteComparison` contains relevant
projective and open comparison claims, but imports this item transitively, so
it cannot be used to prove this item's construction.

## New nodes

`lem-pur-line-counit-comparison` states the all-Noetherian one-step counit
comparison on bounded-below coefficients. The actual source comparison and
actual independent supported-Kummer counit are fixed in its signature.

`lem-pur-ordered-integration-comparison` records the proved ordered-coordinate
induction from that one-step comparison. Its proof uses canonical comparison
naturality and uniqueness of `TowerCounitRecursion`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
