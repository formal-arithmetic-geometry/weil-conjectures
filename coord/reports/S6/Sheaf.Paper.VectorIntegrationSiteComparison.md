## What changed

Only `lean/Sheaf/Paper/VectorIntegrationSiteComparison.lean` and its existing DAG node
are changed. All public signatures, definitions, attributes and public imports are preserved.

Proved `openCounitComparison` using the proved derived extension-unit mate equation from
`Sheaf.SixFunctors.ComparisonOpenTensorCoherence`. A proved private categorical helper derives
the counit square from the unit square by adjunction injectivity, naturality and the triangle
identities. The final calculation transports this square through the canonical exact versus
left-derived pullback comparisons. The argument admits arbitrary schemes and unbounded inputs.
The dependency is a proof-only `import all`, needed to reuse the existing proved private mate
helper; it does not expose new declarations to importers.

Proved `twistCompatibility` by the three corresponding clauses of the already proved finite
Tate site descent theorem. Proved `finiteTypeSiteComparison` by deriving Noetherianity and
invertibility of the coefficient prime, then applying this module's existing generic comparison
statements at the requested arbitrary coefficient index. This last proof is assembly from the
remaining named theorem holes, rather than a proof of those geometric statements.

The DAG records the completed arguments and their actual dependency, while retaining the
planned dependencies for the four untouched geometric theorem holes.

## Proved and sorry left

Original holes: 7. Closed: 3. Added: 0. Split off: 0. Remaining: 4.
All declaration names below have namespace
`AlgebraicGeometry.ProEtale.VectorIntegrationSite`.

Closed holes:

- `openCounitComparison`.
- `twistCompatibility`.
- `finiteTypeSiteComparison` (from the generic comparison statements).

The proved private helper is `counit_square_of_unit` and contains no holes.

The original named theorem holes left untouched are:

- `projectiveComparison`.
- `vectorIntegrationSiteComparison`.
- `vectorTensorComparison`.
- `vectorExponentIndependence`.

Each remains attached to `lem-pur-vector-integration-site-comparison`, with its original
source and full natural-language proof. No new theorem, definition, or other module contains
an added sorry.

## No longer needed

No nodes or modules are withdrawn. In particular, the P1, affine-tower, frame-descent and
exponent-transport nodes remain relevant to the four unfinished clauses; absence of a Lean
proof import is not claimed as their withdrawal. The open-counit clause itself no longer needs
the finite-field P1 transport statement: it follows from the existing general derived mate.

Removed unused proof-only imports (some remain available transitively through unchanged
public imports, so removal of these import lines alone does not imply pruning their modules):

- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `Sheaf.Paper.PurTwistSheafLocallyFree`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.Paper.CompactSupportSiteCoherence`.
- `Sheaf.Paper.RingedExchangeTensorCoherence`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
- `Sheaf.Paper.DegreeZeroDerivedMapGluing`.

## Where the brief, the DAG or earlier work was wrong

The DAG's short assembly does not directly prove the generic declarations in this module.
`p1KummerTraceSiteTransport`, `affineTowerIntegrationSiteTransport` and
`integrationExponentTransposeTransport` specialize to a finite-type scheme over the fixed
finite-field setting and to `P.extension` at index `P.level - 1`. The unfinished declarations
here quantify over arbitrary Noetherian schemes with ell invertible and arbitrary finite
extensions `E`. The coefficient index in the finite-type wrapper is also arbitrary. The
finite-field specialization does not supply a structure map for such a generic base.

The tower interface also requires `LineComparison`, phrased as equality of rank-one ordered
integration, whereas the P1 transport lemma directly supplies the restricted affine trace
equation. Connecting these requires the tower-counit recursion and the source comparisons.

No false statement is asserted and no signature is weakened. The completed proofs avoid these
scope gaps. The generic supported-Cartier Chern comparison, ordered trace comparison,
coefficient-first projection/purity construction and exponent comparison remain genuine work.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
