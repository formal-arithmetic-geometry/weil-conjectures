## What changed

Replaced the single hole in
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.integrationExponentTransposeTransport`
by a proof assembling projective, affine, vector and tensor transport. The public
theorem signature is unchanged. Inverse-decomposition and trace identities follow
from the forward projective square by cancellation. Pro-etale vector trace
independence comes from the existing `vectorExponentIndependence`; the assumed
trace comparison and naturality of the fixed compact-support comparison reflect
it to the ordinary site.

The tensor proof constructs actual transpose isomorphisms from the existing
single-exponent `vectorTensorComparison` data: ordinary purity, boundedness,
the comparison unit and the fixed bounded transpose formula supply all fields.
Coefficient projection naturality and vector trace transport give the integration
squares; adjunction naturality gives the ordinary transpose square, the fixed rho
formula gives the pro-etale square, and cancellation gives both inverse squares.
No data are chosen from a bare existence theorem: the existing data fields fix
each map by its canonical projection, integration or adjunction formula.

Extracted every original coordinate definition verbatim into the new publicly
re-exported `IntegrationExponentTransposeData` module. Added the forward-square
predicate and three strictly smaller geometric or naturality statements in their
own modules. No existing module other than the item is edited. No definition
contains a hole. The original docstrings are preserved.

Validation: all five submitted Lean modules compiled through `lcompile.py`.
The final main-module check passed with no warnings in 23.7 seconds. The complete
projection-naturality proof compiled in 9.0 seconds, the revised affine statement
in 3.8 seconds and the projective statement in 7.6 seconds. The data module also
compiled. No profiler or pretty-printer options remain. The final comparison
naturality proof explicitly unfolds vectorSite and applies the naturality term;
the composition calculations are proved in generic category helpers.

## Proved and sorry left

The item's one original hole,
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.integrationExponentTransposeTransport`,
is closed relative to the imported statements. The new theorem
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.integrationCoefficientProjectionNaturality`
is proved from the naturality of the actual projection transformations, signed
symmetries and tensor-pullback comparison, followed by inverse cancellation.
There are zero holes in the item, the extracted definitions module and the
projection-naturality module. This is a decomposition, not an unconditional
axiom-free proof: two new named holes are added:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.integrationProjectiveExponentSquare`
  (`lem-pur-projective-exponent-square`): only the forward decomposition squares.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.integrationAffineExponentTransport`
  (`lem-pur-affine-exponent-transport`): affine counit and ordered tower transport
  assuming the full projective equations uniformly on Noetherian bases (including
  the recursive affine prefixes).
The existing holes `vectorTensorComparison` and `vectorExponentIndependence` in
`Sheaf.Paper.VectorIntegrationSiteComparison` are reused, not added or modified.
Their strictly narrower independent arguments are attached to new nodes listed
below. Thus the submitted packet closes one original hole and adds two; the
actual dependency-closure counts are for the delivery ledger to compute.

## No longer needed

Removed these original private proof imports from the item:

- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.AlgebraicGeometry.CartierKummerMap`
- `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry`
- `Sheaf.Paper.CompactSupportSiteCoherence`
- `Sheaf.Paper.DegreeZeroDerivedMapGluing`
- `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin`
- `Sheaf.Paper.VectorFrameIntegrationSiteDescent`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`

They are unnecessary as direct imports for the assembled proof. Several remain
transitive dependencies of the preserved definitions or plans for the smaller
statements; their modules and public declarations are not withdrawn. In
particular projective completion, Kummer normalization and ordered integration
are retained through the child arguments, not claimed as pruned mathematics.
The original public imports are preserved in the extracted data module and
re-exported by the item. No modules are withdrawn and no unit step is bypassed.

The original twelve-step proof is replaced by five assembly steps. Direct use of
`lem-pur-affine-tower-integration-site-transport`,
`lem-pur-vector-frame-integration-site-descent` and
`lem-pur-degree-zero-derived-map-gluing` is unnecessary in the item: its global
vector trace clause is already the narrower existing exponent-independence
statement. The child node for that statement retains the actual local-to-global
argument. The tensor single-exponent construction is reused rather than proved
again inside this item.

The complete list of nodes removed from the parent's direct `proof_deps` is:

- `def-pur-finite-site-tensor-projection`
- `def-pur-proetale-frame-integration`
- `def-pur-proetale-ordered-integration`
- `def-pur-supported-projective-site-arrows`
- `def-pur-vector-purity-normalization`
- `lem-amb-affine-space-top-trace`
- `lem-amb-cartier-kummer-map`
- `lem-amb-finite-tate-site-descent`
- `lem-amb-vector-projective-completion`
- `lem-asd-finite-etale-twist-line`
- `lem-cbc-compactification-geometry-fibre-bound`
- `lem-kun-tensor-sym`
- `lem-pur-affine-tower-integration-site-transport`
- `lem-pur-bounded-site-adjunction-transpose`
- `lem-pur-compact-support-site-coherence`
- `lem-pur-degree-zero-derived-map-gluing`
- `lem-pur-p1-kummer-trace-site-transport`
- `lem-pur-projection-comparison-etale-origin`
- `lem-pur-vector-frame-integration-site-descent`
- `lem-weil-finite-compact-projection-formula`
- `prop-weil-pbc-inverse-image-modules-exact`
- `thm-amb-etale-exceptional-adjoint`
- `thm-amb-vector-bundle-purity`

These removals concern the parent proof only. The child plans retain the geometric
steps they use; this list does not authorize deleting any upstream declaration or
withdrawing a module used by another parent.

## Where the brief, the DAG or earlier work was wrong

The item was listed as quarantined for a broken dependency, but its current source
is present. The baseline compile restored the unpublished dependency chain in the
compile tool's private overlay and succeeded. Nothing was withdrawn on that basis.

The combined node `lem-pur-vector-integration-site-comparison` assigns both
`vectorTensorComparison` and `vectorExponentIndependence` while its last proof
step uses this item. Citing that combined node here would introduce a DAG cycle.
The declarations themselves are smaller than the combined statement: one is
single-exponent tensor/site compatibility, the other only pro-etale vector trace
transport. Their independent proofs are now recorded as separate nodes, using no
application of this item's theorem. Their existing Lean declarations and combined
node are unchanged. The new route has no dependency cycle through its new nodes.

Edge cases: rank zero uses the existing zero tensor power and ordered identity;
empty schemes satisfy the same functor equations. No flatness over the prime
power coefficient ring or ramification divisibility is introduced. Every exponent
is still arbitrary subject to annihilating the fixed coefficient quotient.

## New nodes

`def-pur-integration-exponent-transport-data` attaches the unchanged common
coordinate definitions and the new forward-square predicate to the new data
module. It adds no theorem hole.

`lem-pur-projective-exponent-square` is the forward root-normalized decomposition
square on the ordinary and pro-etale sites. The inverse and trace equations are
proved by the item, rather than included in this remaining geometric input.

`lem-pur-affine-exponent-transport` restricts the projective trace via the actual
open counit and inducts through the ordered affine tower, assuming the projective transport family on all Noetherian bases, in particular
each recursive affine prefix. It contains no vector frame descent or tensor transpose conclusion.

`lem-pur-coefficient-projection-naturality` records just naturality of the inverse
coefficient-first projections. This new theorem has a complete Lean proof.
The item supplies the trace, integration,
transpose and inverse-purity consequences.

`lem-pur-tensor-integration-site-data` independently attaches the existing
`vectorTensorComparison` declaration, with a single-exponent proof via ordinary
purity, canonical projection comparison and bounded adjunction transposition.
It creates no new Lean hole and does not depend on exponent transport.

`lem-pur-vector-trace-exponent-independence` independently attaches the existing
`vectorExponentIndependence` declaration, with a proof by local ordered traces
and frame gluing. It creates no new Lean hole and has no tensor transpose clause.

Change record: `coord/changes/G7-integration-exponent-coordinate-extraction.md`.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
