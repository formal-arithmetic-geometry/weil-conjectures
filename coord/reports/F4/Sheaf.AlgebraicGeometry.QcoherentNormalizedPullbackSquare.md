## What changed

Restored the quarantined item with its original theorem signature and a direct simultaneous
effacement proof. The structural tensor-section formula defines the coefficient sheaf morphism.
A finite affine cover supplies an acyclic quasicoherent embedding which stays monic under arbitrary
pullback. Pushing it out along the coefficient map gives a square of short exact sequences.
Naturality follows by induction on degree, using the section normalization in degree zero and the
surjective source boundary in positive degree. A separate comparison square identifies the large
abelian pullback with the specified module cohomology f-map.

New proved modules isolate the geometric embedding, the effacing square, exactness of etale
coefficients, section coherence, the structural sheaf map, the two cohomology maps, the induction,
the resolution comparison square, the general adjunction formula in degree zero, and
the preservation of exact transport and composition under the canonical Ext universe equivalence. Every map is explicitly constructed. Target signatures stay unchanged. The structural section map
now uses a copy uniquely specified to equal its original composition; the equality is proved from
its defining unique equality. This blocks expensive kernel unfolding without changing the map.
The original signature is preserved, and its formula proof and consumers are checked. See
coord/changes/F4-structural-section-map-conversion.md.

The current shared canonical comparison now uses the adopted source resolution modules
and provides component and naturality APIs. This packet preserves that update, including
all its newer public declarations. The canonical comparison module is unchanged by
this delivery. The duplicate Sheaf compatibility module is no longer
in this item's route and is not changed by this delivery.

The large Zariski pullback applies exact inverse image directly in the fixed large Ext
universe. It uses the same direct Mathlib Ext.chgUniv construction as the current canonical
comparison. Universe change commutes with exact-functor transport and Yoneda products. The module comparison square follows from the existing
coefficient and edge squares and this compatibility.


Validation: all thirteen delivery modules compile in one import-ordered lcompile.py --all run,
with zero errors and warnings. The restored item checks in 25.9 seconds; the largest check is
58.9 seconds, below the unchanged 60-second file limit. The existing direct consumer
Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback compiles unchanged against the
final compiled item and structural map (16.9 seconds). A separate import-only axiom check
confirms that the general pullback API and large module-comparison square use only propext,
Classical.choice and Quot.sound. The original item signature is byte-identical. All new-node
Lean signatures match their modules, and each node's proof_deps is the union of its proof uses.
The adopted source library and canonical comparison module are unchanged.

## Proved and sorry left

Closed: AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square,
the item's one original sorry. Added holes: zero. Split off unfinished results: zero.
All eleven new nodes are proved in this packet.
No sorry remains in any new module. The delivery does not claim to close existing holes in
imported declarations; those remain the existing library obligations.

## No longer needed

The new proof replaces the node's direct Cech-refinement plan by simultaneous dimension shifting.
It constructs no additional Cech complex, totalization, edge inverse or refinement representative.
Existing adopted source constructions remain intact, including their Cech dependencies. In
particular the canonical comparison still imports the finite affine Cech basis, tensor Cech
vanishing, Cech comparison and vanishing criterion, module Cech comparison, affine beta
quasi-isomorphism, and the universal effaceable-delta-functor theorem. None of these modules is
claimed pruned merely because the new proof does not invoke it directly.

The large Zariski map is defined directly in the final Ext universe. The argument therefore
needs universe change only for the resolution comparison square, through exact transport and
composition; no separate universe-change boundary or degree-zero section comparison is retained.
The unused general sheaf-level theorem cohomologyPullbackMap_universeChange is also
omitted: the module-comparison bridge applies the general Ext universe-change theorem directly.

The following former dependencies are absent from this item's resulting import closure and are
not needed by its replacement argument:

- lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings (WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings).
- lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites (WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites).
- lem-weil-pbc-etale-cohomology-over-open (Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen).
- lem-weil-pbc-acyclic-cech-edge-compatibility (Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility).
- def-sp-double-complex-total (Sheaf.CategoryTheory.DoubleComplexTotal).
- lem-weil-pbc-ringed-site-cech-refinement-square (Sheaf.CategoryTheory.RingedSiteCechRefinementSquare).
- lem-weil-pbc-sets-etale-inverse-image-exact (WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact).

The separated-affine-open-intersection Mathlib leaf remains useful in the acyclic embedding:
affine intersections ensure that the finite cover's disjoint-union map is affine. The section
map, tensor-section functoriality and naturality, affine cohomology edge, quasi-coherent direct
images, module cohomology f-map, etale cohomology map, and common-resolution normalization and
naturality all remain used, through the dependencies of the new nodes and canonical comparison.


The other removed direct proof imports remain transitively imported and are not pruned:

- WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
- WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
- WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
- WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
- WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
- WeilConjectures.AlgebraicGeometry.EtaleTensorSections
- WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
- WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
- WeilConjectures.AlgebraicGeometry.ModuleCechComparison
- WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
- WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
- WeilConjectures.CategoryTheory.SiteCechMathlibComparison
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

No existing source declaration or quarantined module is withdrawn, and no Lean file is deleted.
The unit sk-thm-properbasechange and all its realized steps remain. Global pruning requires
checking other parents and adopted source uses; this packet makes no global-unreachability claim.

## Where the brief, the DAG or earlier work was wrong

The item was quarantined for duplicate resolution-comparison declarations; it was not
mathematically withdrawn. The current shared canonical comparison imports the adopted
implementation directly. This packet uses that repaired route and preserves its public APIs.

The planned two-cover Cech proof is unnecessary. A naive arbitrary acyclic embedding would not
suffice for a non-flat g: pullback need not preserve its monomorphism. The chosen affine-cover
unit is universally monic, as proved by faithful flat-cover pullback and the adjunction triangle.
This is what makes simultaneous effacement valid without assuming flatness. Acyclicity is needed
only for the source middle term. The target middle term is merely quasicoherent.

## New nodes

lem-weil-pbc-qcqs-quasicoherent-pure-acyclic-embedding: Universally monic quasicoherent acyclic embedding. Module Sheaf.AlgebraicGeometry.QcqsQuasicoherentAcyclicEmbedding, primary declaration exists_qcqs_quasicoherent_pure_acyclic_embedding. The module proves this result in full.

lem-weil-pbc-qcoherent-pullback-effacing-square: A pullback coefficient map extends to an effacing square. Module Sheaf.AlgebraicGeometry.QcoherentPullbackEffacingSquare, primary declaration exists_pullbackEffacingSquare. The module proves this result in full.

lem-weil-pbc-etale-tensor-sections-functor-exact: Exactness of sheafified tensor sections. Module Sheaf.AlgebraicGeometry.EtaleTensorSectionsFunctorExact, primary declaration etaleTensorSectionsFunctor_exact. The module proves this result in full.

lem-weil-pbc-qcoherent-etale-coefficient-exact: Exactness of lifted associated etale coefficients. Module Sheaf.AlgebraicGeometry.QcoherentEtaleCoefficientExact, primary declaration coherentEtaleMap_shortExact. The module proves this result in full.

lem-weil-pbc-qcoherent-pullback-section-square-naturality: Naturality and units of structural section pullback. Module Sheaf.AlgebraicGeometry.QcoherentPullbackSectionsNaturality, primary declaration qcoherentPullbackSection_square_naturality. The module proves this result in full.

lem-weil-pbc-qcoherent-tensor-pullback-sheaf-map: Structural coefficient morphism on lifted etale sheaves. Module Sheaf.AlgebraicGeometry.QcoherentTensorPullbackSheafMap, primary declaration qcoherentPullbackSheafMap_naturality. The module proves this result in full.

lem-weil-pbc-qcoherent-pullback-cohomology-maps: Structural cohomology maps preserve boundaries and sections. Module Sheaf.AlgebraicGeometry.QcoherentPullbackCohomologyMaps, primary declaration zariskiPullbackCohomology_boundary. The module proves this result in full.

lem-weil-pbc-qcoherent-normalized-pullback-naturality: Normalized comparisons commute with structural cohomology pullback. Module Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackNaturality, primary declaration normalizedCoherentEtale_pullback_naturality. The module proves this result in full.

lem-weil-pbc-module-abelian-large-pullback: Large module-to-abelian comparison respects pullback. Module Sheaf.AlgebraicGeometry.ModuleAbelianCohomologyLargePullback, primary declaration moduleAbelianCohomologyLarge_pullback. The module proves this result in full.

lem-weil-pbc-adjunction-cohomology-pullback-zero: Degree zero of an adjunction cohomology pullback. Module Sheaf.CategoryTheory.CohomologyPullbackZero, primary declaration adjointCohomologyPullbackMap_zero_of_eq. The module proves this result in full.

Change record: coord/changes/F4-structural-section-map-conversion.md.

lem-weil-pbc-ext-universe-change: Ext universe change preserves exact transport and composition.
Module Sheaf.CategoryTheory.ExtUniverseChange, primary declaration universeChangeEquiv_exactComposite.
The module proves this result and its represented-morphism compatibility in full.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
