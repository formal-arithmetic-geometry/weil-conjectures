## What changed

The original item signature and public imports are preserved. The proof explicitly constructs
its coefficient sheaf map from the structural section maps and ULift. A restriction-naturality
lemma supplies the presheaf naturality equation. The cohomology proof then composes two
squares and cancels additive equivalences using the proved private lemma combine_squares.

The new QcoherentZariskiCohomologyMap module constructs moduleAbelianHMap sectionwise and
zariskiModuleHMap using exact abelian inverse image, the canonical constant-integer
comparison, and the adjoint coefficient map on Ext. These are explicit constructions;
no data are selected from an unproved mere-existence assertion. The other three new modules
state the remaining strictly separate steps: structural section naturality, module/abelian
h-map compatibility, and normalized abelian Zariski/etale h-map compatibility.
No source-library file or existing public interface changes.

## Proved and sorry left

Decomposition: the former sorry in
AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square is closed
by a complete combining proof. One upper hole is replaced by three lower holes, so this
is a decomposition with net minus two holes, not a completed proof of the mathematics.
The remaining sorries are exactly:

- AlgebraicGeometry.Scheme.Modules.qcoherentPullbackSection_naturality
  (lem-pbc-qcoherent-pullback-section-naturality).
- AlgebraicGeometry.Scheme.Modules.moduleAbelianCohomologyLarge_hmap
  (lem-pbc-module-abelian-hmap).
- AlgebraicGeometry.Scheme.Modules.normalizedAbelianEtale_hmap_square
  (lem-pbc-abelian-etale-hmap-square).

Each has one public theorem in a separate module, a complete source-based proof in words,
and a matching DAG node. Section naturality contains no cohomology or quasi-coherence.
The module/abelian bridge contains no etale comparison or quasi-coherence. The abelian
change-of-site square has neither the module-derived h-map nor the existence of theta.
The explicit construction and cancellation in the item are real Lean proofs; none of
these statements is the item renamed.

## No longer needed

Removed direct proof imports:

- WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherentULift
- WeilConjectures.AlgebraicGeometry.EtaleAffineTensorCechVanishing
- Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen
- WeilConjectures.AlgebraicGeometry.EtaleFiniteAffineCechBasis
- WeilConjectures.AlgebraicGeometry.EtaleTensorSections
- WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
- WeilConjectures.AlgebraicGeometry.ModuleCechBetaAffineQuasiIso
- WeilConjectures.AlgebraicGeometry.ModuleCechComparison
- WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
- Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
- WeilConjectures.CategoryTheory.DoubleComplexTotal
- Sheaf.CategoryTheory.RingedSiteCechRefinementSquare
- WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
- WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
- WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
- WeilConjectures.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings
- WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
- WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal
- WeilConjectures.CategoryTheory.SiteCechMathlibComparison
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

The old blanket proof imports are replaced by the three precise proof interfaces. Some of
these modules and mathematical inputs remain below the new abelian comparison node;
they are not claimed globally pruned. No module is withdrawn. The item's DAG proof_deps
now names only the structural map and the three steps actually used by its Lean proof.

The general ringed-site refinement-square node
lem-weil-pbc-ringed-site-cech-refinement-square is not used by the replacement route.
The new abelian step fixes the structural tuple map and uses its resolved construction,
rather than importing that generic arbitrary-gamma assertion. The direct source dependencies
lem-weil-pbc-zariski-etale-inclusion-morphism-of-sites,
lem-weil-pbc-affine-morphism-cohomology-edge, and
lem-pc-sections-higher-direct-image-quasi-coherent are also omitted from this decomposition.
The common-resolution normalization and coefficient naturality inputs remain needed below
the appropriate new nodes. The blueprint unit statement and its realized steps are preserved;
this changes only the argument below the unit.

## Where the brief, the DAG or earlier work was wrong

The planned RingedSiteCechRefinementSquare route uses
ringedSite_cech_refinement_square_rest, already marked STATEMENT-DISPUTED in its module:
it allows arbitrary gamma instead of requiring the structural refinement tuple formula.
Identity site and coefficient map with gamma zero contradict its degree-zero square.
This delivery neither changes nor relies on it. The abelian replacement plan specifies the
structural tuple map, as in Stacks cohomology.tex lemma-functoriality-cech.

The available section-map definition has no public theorem for naturality under base change.
The fixed module/abelian comparison's coefficient naturality is not yet its naturality under
an arbitrary scheme h-map. Those are different statements and are separated here. Existing
Cech and delta-functor interfaces likewise do not directly supply the abelian h-map square.
The new statements cover these precise gaps without strengthening the original hypotheses.
The empty scheme, zero coefficient and degree-zero cases agree with the proposed formulas;
no assertion that inverse images of affine opens are affine is used.

## New nodes

lem-pbc-qcoherent-pullback-section-naturality is the structural section restriction step,
without any cohomology or quasi-coherence hypotheses.

def-pbc-qcoherent-zariski-cohomology-map records the explicit construction of the abelian
Zariski h-map and its sectionwise coefficient map. It contains no sorry.

lem-pbc-module-abelian-hmap is the fixed common-resolution comparison's compatibility
with arbitrary module h-maps, independently of change of site.

lem-pbc-abelian-etale-hmap-square is the remaining abelian change-of-site square with a
given coefficient map satisfying its structural component formula. It retains the finite
affine cover, affine vanishing and normalized delta-functor argument from the original plan.

All four nodes retain the item's chapter and unit and record the source, searches and proof
steps. No existing signature or definition was changed, so no change record is required.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
