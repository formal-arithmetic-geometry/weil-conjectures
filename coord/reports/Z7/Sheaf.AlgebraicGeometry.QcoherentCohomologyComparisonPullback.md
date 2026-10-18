## What changed

Reduced `exists_qcoherentCohomologyComparisonPullback` to normalized comparison
existence on a single quasi-compact separated scheme and its Cech refinement
square for an arbitrary scheme morphism. The simultaneous family is assembled
by choosing the uniquely normalized family scheme by scheme and inverting it.
The degree-zero clause follows by cancellation of the comparison and the
section equivalence. Scalar compatibility follows by specializing direct
coefficient naturality on module cohomology to multiplication and cancelling
the chosen equivalence.

Moved the unchanged definition `qcoherentPullbackSection` into the new public
support module to allow the refinement-square statement to mention the formula
without an import cycle. The original module publicly imports it. The change
record documents the identical old and new definition and its consumers.
No original theorem signature, universe, or visibility changed.

Validation: `lcompile.py --all` compiled all four delivery modules. The original
theorem signature was checked unchanged modulo whitespace. The combining proof
uses local opacity for the fixed section and cohomology maps to prevent expensive
unfolding; no definition body or exported transparency is changed.

## Proved and sorry left

Original holes closed:

- `AlgebraicGeometry.Scheme.Modules.exists_qcoherentCohomologyComparisonPullback`
  now has a complete combining proof.

Holes added, each in a separate new module:

- `AlgebraicGeometry.Scheme.Modules.exists_unique_qcoherentNormalizedComparison`
  (node `lem-weil-pbc-qcoherent-normalized-comparison-exists`).
  Still needs the finite-affine-Cech comparison with connecting morphisms,
  agreement with the fixed module/abelian resolution comparison, and uniqueness
  by quasi-coherent effacement. Direct coefficient naturality also needs
  naturality of the common-resolution comparison and of Ext universe change.
  Ordinary degreewise comparison alone does not
  supply the required connecting-map compatibility.
- `AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square`
  (node `lem-weil-pbc-qcoherent-normalized-pullback-square`).
  Still needs the two normalized Cech edge squares, the tuplewise identification
  of their maps, and identification of their derived maps with the prescribed
  etale and module maps. It also needs the sectionwise coefficient sheaf map:
  unit/composition coherence and coefficient naturality must give its restriction
  squares, followed by coefficient lifting.

This is a decomposition of one original hole into two strictly separate
obligations, not a claim of a net reduction in sorry count. The structural
formula, scalar clause, zero clause, and combining proof have no holes.
There are two remaining sorry declarations in this delivery.

## No longer needed

The scalar argument does not need
`lem-weil-pbc-cohomology-pullback-functorial` or its module
`WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`:
it uses coefficient naturality directly, rather than specializing the
arbitrary-pullback identity and simplifying an identity pullback.

The original file's following proof-only imports are removed. Apart from the
identity-pullback argument just described, this does not claim that their
mathematics is transitively unnecessary: the two new obligations retain the
finite affine cover, affine acyclicity, normalized edges, and refinement-square
route, with these dependencies recorded in their nodes.

- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
- `WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites`
- `Sheaf.AlgebraicGeometry.EtaleAffineQcoherentULift`
- `Sheaf.AlgebraicGeometry.EtaleFiniteAffineCechBasis`
- `Sheaf.AlgebraicGeometry.EtaleAffineTensorCechVanishing`
- `WeilConjectures.CategoryTheory.SiteCechMathlibComparison`
- `WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion`
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.ModuleCechComparison`
- `Sheaf.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso`
- `Sheaf.CategoryTheory.DoubleComplexTotal`
- `WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact`
- `WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.CategoryTheory.RingedSiteCechRefinementSquare`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`

## Where the brief, the DAG or earlier work was wrong

The existing canonical normalized comparison is stated only for a proper
scheme over a field, whereas this item quantifies over every quasi-compact
separated scheme. It cannot be applied to the item's general schemes.
The ordinary etale/Zariski and coefficient-universe comparisons do provide
degreewise isomorphisms and coefficient naturality, but their statements do
not assert compatibility with connecting morphisms. Choosing those components
independently is insufficient to deduce the normalized delta-functor predicate.
The new existence obligation explicitly retains that missing requirement.
These are interface gaps, not claims that the existing statements are false.

The delivery tool reports that it filters the proposed addition of the new
section-formula node to the original node's `stmt_deps` as a field outside the
worker's delivery permissions. The sandbox records that dependency; the
maintainer should retain it when reviewing the definition move. The new square
node also explicitly records the section-formula node among its dependencies.

No forced adaptation of another group's module was necessary. No target or
mathematical definition was weakened. Empty schemes and zero coefficients are
included in both new statements; arbitrary pullback is not assumed flat.

## New nodes

- `lem-weil-pbc-qcoherent-normalized-comparison-exists`, module
  `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison`:
  normalized comparison and uniqueness on one scheme.
- `lem-weil-pbc-qcoherent-pullback-sections-map`, module
  `Sheaf.AlgebraicGeometry.QcoherentPullbackSections`:
  the unchanged structural tensor-section formula, moved to a separate
  module so the compatibility statement can mention it without a cycle.
- `lem-weil-pbc-qcoherent-normalized-pullback-square`, module
  `Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare`:
  the coefficient sheaf map and cohomology refinement square for given
  normalized comparisons.

The original node's proof and dependencies describe the Lean combining proof.
Each new node records its statement, sources, complete proof plan, and the
searches made before introducing it.

Change record: `coord/changes/qcoherent-pullback-section-module.md`.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
