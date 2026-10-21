## What changed

Retire the assigned zero-hole duplicate Sheaf.CategoryTheory.DoubleComplexTotal
in favour of the fully proved WeilConjectures.CategoryTheory.DoubleComplexTotal.
The 16 current direct importers migrate with their original import visibility;
CanonicalFiltration preserves the compatibility API. The existing mathematical
node is attached to the source realization. Its statement, dependencies, proof
plan and unit route are unchanged. No source-library declaration or target changes.
See coord/changes/S2-retire-double-complex-total.md.

Repair the return at a81b6d35e by explicitly recording
Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero in the change record's
Users table. It uses coherentExtUniverseEquiv and
moduleAbelianCohomologyLarge through current main's proved component API.
Current main's canonical comparison module, component/naturality lemmas and node
are preserved verbatim. The earlier sandbox comparison/effacement optimizations
and their two stale records are omitted from this rebased packet. No definition
in that API is changed by this delivery.

The now-restored QcoherentNormalizedPullbackSquare receives the import migration.
Current main's other restored comparison consumers already use the adopted source
naturality API and are unchanged. Current main's RingedSiteCechRefinementSquare
has a newer proof and no retired import, so its stale sandbox adaptation is omitted.
Seven other stale adaptations are omitted because they add only imports that are
already available through current main. No quarantine archive is deleted or restored.

## Proved and sorry left

Zero-hole retirement: 0 of 0 sorries proved; 0 added; 0 split off.
The withdrawn module and its adopted twin have no sorry. This is a module pruning,
not a reduction of a theorem hole. The 15 pre-existing holes in import-only adapted
consumers remain unchanged:

- CategoryTheory.filteredInjectiveResolution
  (lem-trf-filtered-injective-resolution).
- DerivedCategory.exists_source_hyperExt_module_target
  (lem-trf-source-hyperext-module-target).
- CategoryTheory.acyclic_hom_of_coproduct_ext_orthogonal
  (lem-trf-acyclic-coproduct-ext-orthogonal-hom).
- HomologicalComplex₂.boundedBelow_cech_cone_comparison
  (lem-trf-bounded-below-cech-cone-comparison).
- HomologicalComplex₂.cartanEilenberg_properties
  (lem-sp-cartan-eilenberg-properties).
- CategoryTheory.SimplicialSlice.site_augmentation_spectral_sequence
  (lem-trf-site-augmentation-spectral-sequence).
- AlgebraicGeometry.Scheme.Modules.qcoherentNormalizedComparison_pullback_square
  (lem-weil-pbc-qcoherent-normalized-pullback-square).
- AlgebraicGeometry.simplicial_etale_restriction_exact.
- AlgebraicGeometry.simplicial_etale_morphism_direct_image.
- AlgebraicGeometry.simplicial_etale_derived_component.
- AlgebraicGeometry.simplicial_derived_image_spectral_sequence.
- AlgebraicGeometry.simplicial_etale_direct_image_composition.
- AlgebraicGeometry.simplicial_etale_composite_adjunction_normalization.
- AlgebraicGeometry.simplicial_etale_augmented_diagram_comparison.
- AlgebraicGeometry.simplicial_etale_augmented_adjunction_normalization.

The eight simplicial declarations belong to
lem-trf-simplicial-derived-image-spectral-sequence.

The retained filtration compatibility audit reconstructs both old definitions and
proves their step and graded-piece equalities by rfl, for arbitrary integer indices.
It passes again in 1.7 seconds, including its 14 source-declaration axiom probes;
only propext, Classical.choice and Quot.sound occur. Negative degrees and empty
intervals require no added hypothesis. The final 16-module sandbox batch passes with artifact generation, in
1.7–26.8 seconds per module. The restored normalized pullback-square consumer
passes in 13.1 seconds. The delivery tool performs its own standard checks.

## No longer needed

Pruned module: Sheaf.CategoryTheory.DoubleComplexTotal, including its two duplicate
filtration constructions, 12 public theorem proofs and private helpers. All 16
current direct imports are migrated, including the import-all occurrence in
DoubleComplexTruncationDecalage. The proved source total-complex module,
PBCFiltration and CanonicalFiltration remain needed. No mathematical node,
parent dependency, or unit step is withdrawn: the same node is realized by the
adopted source module, including for planned parent proofs.

The earlier sandbox canonical-comparison and effacement adaptations are unnecessary
on the current base and are omitted, preserving the newly landed degree-zero and
naturality API. No additional module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is the zero-hole retirement listed in coord/retire-items.tsv. It already
had complete proofs; the stale node note described the former statements as sorry.
The relevant representation difference is DecreasingFiltration versus
PBCDecreasingFiltration, with definitionally equal steps and cokernels. The node's
Lean attachment records this accurately, without weakening its statement.

The returned packet's Users inventory missed the newly landed degree-zero consumer.
That consumer is now explicitly listed. Current main also restored the normalized
pullback-square consumer and proved a theorem in RingedSiteCechRefinementSquare;
the packet is rebased to preserve both developments. Two attempted comparison
construction validations exceeded the ordinary limit; those exploratory
constructions are omitted entirely. No compile limit was increased and no file or
proof was split. No declaration from WeilConjectures is removed or modified.

## Forced adaptations

No consumer currently held by another group is adapted. All changes to active
consumer Lean files are import-only and preserve their signatures and proof bodies.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
