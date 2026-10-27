## Worker report

States `AlgebraicGeometry.AlgebraicSpace.spectralSpace_of_compact_of_absolutelyQuasiSeparated`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQcqsSpectral`. Its only proof is `sorry`.
The theorem docstring carries all four steps of the accepted proof, with the nodes
used at each step. No definitions or additional theorems are introduced.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`; any base scheme is allowed.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, the recorded fppf-sheaf
  definition with representable diagonal and a representable surjective etale atlas.
- Field-valued point classes with the atlas topology: `Point X.obj.obj`, with
  `AlgebraicSpace.pointTopologicalSpace` inferred from the existing definition.
  That topology is the final topology for representable etale scheme charts.
- The size convention: explicit `universe u`, `Scheme.{u}`; the existing Point
  definition lives in `Type (u + 1)`. No independent test-scheme universe or
  equality between universes is added; all variables are explicitly bound.
- Every open cover has a finite subcover: `(hqc : CompactSpace (Point X.obj.obj))`.
  Mathlib compactness here has no Hausdorff condition.
- The absolute diagonal is quasi-compact on affine scheme tests:
  `(hqs : IsAbsolutelyQuasiSeparated X)`. This is the existing definition from
  `def-sfb-space-absolute-quasi-separated`. Its affine-pair fibre-product condition
  is equivalent to the node's absolute-diagonal condition by Stacks 0AHR(1),(3),
  read in `spaces-properties.tex`, lemma-characterize-quasi-separated. The
  criterion quantifies over every pair of affine S-schemes mapping to X,
  not only etale charts. This is absolute quasi-separatedness even for a
  non-quasi-separated base. The existing definition node is added to stmt_deps.
- Conclusion: `SpectralSpace (Point X.obj.obj)`. As the recorded spectral-space
  node specifies, Mathlib's class extends `CompactSpace` (quasi-compactness),
  `T0Space` and `QuasiSober` (existence and uniqueness of the generic point of
  each nonempty irreducible closed subset), `PrespectralSpace` (compact opens
  form a basis), and `QuasiSeparatedSpace` (compact open intersections compact).
- No Noetherian, finite-type, separation, nonemptiness, field-base or fixed-atlas
  hypothesis occurs in the signature.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentableWith`, `IsAlgebraicSpace`, `IsEtale`, `IsSurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`, with the existing
  `Point` and `schemePointMap` from `AlgebraicSpacePointClasses`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.
- `Mathlib.Topology.Spectral.Basic`: `SpectralSpace`; its component definitions
  in `Topology.Spectral.Prespectral`, `Topology.Sober` and
  `Topology.QuasiSeparated` render the four clauses above.
- `def-weil-size-convention` is a recorded metatheoretic convention with no
  declaration to import; it is rendered by the explicit universes.

The public imports supply the statement interface. Plain proof imports cover
all currently recorded proof modules: `SpaceQuasiCompactAffineTests`
(its four quasi-compactness criteria), `AlgebraicSpaceAffineEtaleCover`
(`exists_affine_etale_cover_and_point_topology`), `AlgebraicSpacePointOpenCalculus`
(`point_open_calculus`), and the Mathlib matches for etale composition,
quasi-compactness and quasi-separatedness of affine schemes, the affine-open
basis, and `isCompact_range`. The three proof prerequisites
`lem-sfb-quasiseparated-space-sober`, `lem-sfb-qc-space-affine-etale-atlas` and
`lem-sfb-space-affine-source-qc-separated` currently have no Lean binding in the
read clone, so no unrecorded module was guessed for them. They are proof-only
prerequisites; this delivery needs no missing statement notion.

Edge cases checked before writing: the empty space (empty open and finite
covers allowed), empty intersections, a one-point space, arbitrary non-Noetherian
qcqs spaces, and a non-separated or non-quasi-separated base. The use of absolute
quasi-separatedness is essential to preserve the last case; no relative-only
replacement was made. No edge case requires changing the node or adding a hypothesis.

Sources read: Stacks `spaces-properties.tex`,
`lemma-quasi-compact-quasi-separated-spectral` (Tag 0A4G), full proof, and
`lemma-characterize-quasi-separated` (Tag 0AHR), statement and proof. The latter
justifies using the already accepted affine-test definition directly.

Searches actually run through msearch.py for this group/item:

- LeanFinder: `A quasi compact quasi separated algebraic space has a spectral point topology`.
  Eight hits concern schemes or scheme morphisms, including
  `AlgebraicGeometry.quasiCompact_iff_spectral`; no algebraic-space theorem.
- Loogle: `SpectralSpace`. Nine hits give the class, projections, constructor,
  open-embedding theorem and PrimeSpectrum instance; no result about spaces.
- Mathlib grep: `spectralSpace|SpectralSpace|AlgebraicSpace` in AlgebraicGeometry.
  Four hits concern scheme prespectrality and flat descent, not this theorem.
- LeanSearch: `A quasi compact quasi separated algebraic space has a spectral underlying topology`.
  Eight hits concern spectral-space projections, the constructor, and schemes.
- Local rg/grep of `lean/WeilConjectures` for the item id and algebraic-space
  spectrality names found no declaration. Local rg of `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the proposed name and algebraic-space
  spectrality found only downstream references in proof docstrings, no theorem.
  The broader algebraic-space quasi-separatedness search found the existing
  `IsAbsolutelyQuasiSeparated` definition, which is used instead of duplicated.

The standalone scompile.py run compiled both sandbox and library forms cleanly
(1.7 and 1.6 seconds). No statement dispute or node correction is needed.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
