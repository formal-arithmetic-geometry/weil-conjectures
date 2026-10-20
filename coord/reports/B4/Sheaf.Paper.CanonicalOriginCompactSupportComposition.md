## What changed

Proved the four existing holes in `Sheaf.Paper.CanonicalOriginCompactSupportComposition`.
The public statements and all existing data constructions are unchanged. Private proved
helpers compute fully faithful descent and transport the existing etale unit and
associativity laws along the specified natural site comparisons. The retained-witness
proof uses the derived unit of the canonical coefficient equivalence and the original
witness alpha, retaining its etale complex.

Updated `thm-sf-comp-composition` only in its proof, proof dependencies,
and proof origin. No new modules, nodes, axioms, or definition
repairs are introduced. The import and local proof-attribute changes are documented
in `coord/changes/B4-canonical-origin-composition-proof-scope.md`. The adopted WeilConjectures source tree is untouched.

Validation: the complete module compiled through lcompile.py in 17.4 seconds, with
all four proofs present. The only diagnostic warnings concerned the temporary
profiling and reduced-heartbeat options; those options have been removed. Local
irreducibility attributes keep the large chosen comparison isomorphisms folded
during unification without changing their definitions or exported attributes.

## Proved and sorry left

Closed 4 of 4 existing holes (node `thm-sf-comp-composition`):

- `AlgebraicGeometry.ProEtale.originComposition_id_left`.
- `AlgebraicGeometry.ProEtale.originComposition_id_right`.
- `AlgebraicGeometry.ProEtale.originComposition_assoc`.
- `AlgebraicGeometry.ProEtale.originWitnessFixed_property`.

Holes added: zero. Holes remaining in the item: zero. Split off: zero.
The private comparison and category calculations are proved in this same module.
Existing imported obligations retain their existing declarations and nodes.

## No longer needed

Removed these 18 private proof imports:

- `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`.
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`.
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`.
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`.
- `Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle`.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`.
- `Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`.
- `Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.Paper.FiniteDirectImageComposition`.
- `Sheaf.Paper.RefinementComparisonIsomorphism`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `WeilConjectures.Compactification.Refinement`.

All original public imports remain. The private import of
`Sheaf.Paper.CompactificationCoherence` remains because it belongs to the unit route;
its declarations and the corresponding statement dependency are preserved. The
unit and associativity calculations reuse the existing etale compactification
compositor and its coherence, transported by the specified site comparisons.

The following old immediate proof dependencies are no longer needed as separate
steps of this module's proof (they may remain needed inside the reused constructions):

- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `lem-weil-pbc-qcqs-morphism-permanence`.
- `lem-weil-extension-by-zero-exact`.
- `lem-sf-comparison-pullback-exact`.
- `lem-cbc-proetale-extension-zero-comparison`.
- `prop-weil-pbc-comparison-direct-image`.
- `thm-nagata-compactification`.
- `lem-weil-pbc-compatible-compactification-triangle`.
- `def-weil-compactifications-refinements`.
- `lem-weil-extension-by-zero-adjunction`.
- `lem-cbc-proper-open-interchange-coherence`.
- `lem-sf-proper-open-comparison-site-normalization`.
- `def-sf-refinement-comparison-isomorphism`.
- `lem-weil-derived-direct-image-composition`.
- `lem-cbc-compactifiable-compatible-tower`.
- `def-pc-fibre-product`.

No module or declaration is withdrawn. The etale compact-support interface is used
through its existing upstream declarations; its extra Sheaf wrapper import is not
needed. Similarly the canonical origin equivalence already provides the required
fully faithful interface without a direct CompactSupportComparisonUnit import.

## Where the brief, the DAG or earlier work was wrong

The old proof/import plan repeated geometry already available in the declared
upstream etale compositor. The shorter proof transports its specific equations via
the comparison maps already used in this module's definitions. No statement or source
correction is needed. The unit record has no separately realized steps to bypass;
the reused etale construction follows its proper/open compactification route.

The requested leanfinder, loogle, and grep searches were run through msearch, followed
by direct searches in the adopted library and Mathlib. The useful match is the
existing etale LowerShriekComposition interface; no new mathematical statement is
needed. A dependency-graph search found no back path to this node from the newly used
canonical site-comparison, etale compact-support, or coefficient-realization nodes.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
