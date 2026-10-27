## What changed

Replaced the sole original hole,
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorComparison`, by a Lean
assembly of projection comparison, the already proved global trace comparison, the generic
bounded adjunction transpose calculation, ordinary purity, and ordinary normalization.
Its statement is unchanged. The integration square is proved by a categorical cancellation
and tensor-naturality calculation. The pro-etale and ordinary integration arrows are the
specified composites, and all fields of `TensorCompatibilityData` are supplied.

Added `Sheaf.Paper.VectorTensorProjectionComparison`, which proves the needed boundedness
using finite Tor amplitude and obtains the ordinary projection inverse from existing
purity. It applies the separate compact-support square with inverse comparison to
obtain the pro-etale projection isomorphism and its actual-map equation. That square and
ordinary normalization are the two remaining statements. They have independent modules,
complete proof descriptions, sources, and DAG nodes. The square's proof description
constructs pp explicitly and identifies its inverse by cancellation; its statement fixes
that inverse to the actual projection map.

Added only private proof imports to the existing item. Its other proofs, public signatures,
public imports, definitions, and instances are preserved. Local transparency annotations
in the new proof section avoid unfolding the large derived-category constructions. The
private proof-sharing metaprogram abstracts nested instance proofs using Lean's ordinary
cache, following `ProjectionComparisonEtaleOrigin`; the resulting term is kernel checked.
No other existing Lean module is changed.

## Proved and sorry left

Closed original hole (one of one):
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorComparison`.
The item has zero remaining holes.

Added two holes, so this is a decomposition, not a net reduction in admitted statements:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.coefficientFirstCompactSupportSiteSquare`,
  node `lem-pur-coefficient-first-compact-support-site-square`, in
  `Sheaf.Paper.CoefficientFirstCompactSupportSiteSquare`.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorOrdinaryNormalization`,
  node `lem-pur-vector-tensor-ordinary-normalization`, in
  `Sheaf.Paper.VectorTensorOrdinaryNormalization`.

`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorProjectionComparison` has a
complete proof from the first of these statements and existing ordinary purity. It adds
no hole. Neither remaining lemma asserts the original integration and transpose equations:
the first concerns only actual projection maps for the vector compactification; the second
concerns only the ordinary adjunction and normalization. The parent combines these parts
by real categorical calculations. No private theorem or definition contains `sorry`.

Both statements were checked against rank zero, the empty base, zero objects, arbitrary
annihilating positive moduli, and ramified finite coefficient rings. They impose no
finite-field hypothesis or flatness over Z/N. Existing admitted library dependencies,
including `vectorBundleNormalized`, retain their own nodes and are not duplicated here.

## No longer needed

Removed `lem-pur-integration-exponent-transpose-transport` from this node's proof
dependencies. Its public statement assumes a finite-field finite-type base and fixed
coefficient index, whereas the tensor clause is over arbitrary Noetherian bases and
indices. Moreover, its current module imports this item and its private `transpose_data`
uses `vectorTensorComparison`, so importing it here would create a cycle. This removes
one obsolete dependency from this proof; the transport module is not withdrawn.

No existing Lean import is removed and no existing module is withdrawn. The earlier
ordered integration, supported Chern comparison and local exponent-transition dependencies
remain needed. The new projection proof imports the compact-support square rather than
importing its proper/open and braiding proof dependencies itself; those remain the
remaining square's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The proposed tensor route through `integrationExponentTransposeTransport` does not cover
the item's general base and coefficient parameters and now points in the wrong import
direction. The new reduction uses the generic proper/open compact-support square and the
private generic `boundedSiteTranspose_compatible` calculation instead. No statement is
weakened and the unit route is preserved.

Direct implementation of the two lower calculations ran into expensive conversion between
the native derived monoidal structure and the cached etale tensor functors. Generic
coefficient-category symmetry, unit and adjunction calculations were verified during
experimentation; their specialization and the proper/open coefficient-first pasting did
not meet the checking limit. The delivery leaves these precise steps as the two public
statements above, rather than retaining unfinished local proofs or changing shared
structures. The main assembly was generalized to an arbitrary finite coefficient ring
before specializing to the Tate quotient, which made its kernel checking practical.

## New nodes

`lem-pur-coefficient-first-compact-support-site-square` states the coefficient-first
proper/open projection square in inverse form for the vector compactification. Given the
ordinary projection inverse and boundedness of W and the twisted pullback, it supplies the
actual pro-etale projection inverse and its comparison equation. It has no integration or
transpose conclusion, and assumes no finite Tor amplitude or constructibility of K.
Its proof describes
naturality of the proper/open comparison, both tensorator-braiding squares, the explicit
composite defining pp, and cancellation identifying its inverse. It is the first
remaining hole.

`lem-pur-vector-tensor-projection-comparison` is proved from that square, finite-Tor
boundedness and ordinary purity. It proves both required tensor-order boundedness
properties and supplies the specified ordinary inverse before applying the
square with inverse comparison.

`lem-pur-vector-tensor-ordinary-normalization` states the ordinary signed-symmetry conversion
of the existing normalized purity family. Its proof uses projection cancellation, symmetry
naturality, the finite-unit identity, and adjunction naturality. It is the second remaining
hole and contains no site-comparison or pro-etale conclusion.

No change record is required: no existing statement or definition is repaired.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
