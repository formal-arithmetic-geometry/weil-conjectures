## What changed

Integrated the supplied, compiled shift-saturated route in `SmoothProperDiagonalTensorFormula` and `RightAdjointTensorComparisonProjection`. Both existing public theorem signatures and their public imports remain byte-for-byte unchanged (checked on the raw declaration signatures). The comparison remains the specified global natural adjunction mate, including the pinned inverse equations. Use the predicate `∀ n : ℤ, IsIso (τ.app (K⟦n⟧))`, the separate exact functor structures and the five-term cone argument. Perfect generation then gives invertibility of the original mate.

New proved helpers: `Sheaf.CategoryTheory.ShiftSaturatedIsoLocus`, `Sheaf.AlgebraicGeometry.DerivedExactStructures`, and `Sheaf.AlgebraicGeometry.PerfectLocalizingIsoLocus`. The generic five-term proof and the perfect-object stability proofs retain attribution to their earlier private library proofs. Proof-only imports are private; statement dependencies are public. No experimental `Route` namespace or import remains.

Withdraw the assigned module and its 27 now-unused upstream consumers listed below through `deleted.txt`. The delivery tool lands empty modules, and the existing DAG nodes remain, with their Lean attachment removed by `lean: null`. The complete reverse-import audit shows that every remaining client is adapted in this same delivery. All 29 other existing modules touched by the withdrawal/reroute are currently unclaimed; the assigned module belongs to P3. This uses the explicit unclaimed-module adaptation rule, so no claimed module is altered.

Validation: all seven sandbox Lean files compile cleanly using `lcompile.py --all`, including unchanged copies of `RightAdjointTensorComparisonNatural` and `PerfectImmersionTensorAcrossUniverses`. The unchanged copies are validation clients and are not changes delivered to the library. The full import audit from `TargetsCheck` removes 62 Sheaf modules (66 imported modules including four non-Sheaf modules); the assigned item is absent afterward. No outside importer of a withdrawn module remains. No target statement or target-visible definition changes. The unit `sk-thm-picard-duality` route is preserved.

## Proved and sorry left

Original assigned hole `AlgebraicGeometry.exists_flat_telescope_cone_normalization_descent` (`lem-sc-flat-telescope-cone-normalization-descent`): **not proved**; withdrawn as an unnecessary obligation of the old route. This delivery is pruning, not a decomposition or a proof of that stronger statement. Of the original one sorry, zero are proved, zero are split off, and one is retired from the active import closure.

New direct holes: none. Every theorem in all three new helper modules has a complete proof; their main declarations and subsidiary APIs are:

- `CategoryTheory.ShiftSaturated.isoOnThirdOfIsoOnFour` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts_of_iso` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts_shift` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts_retract` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts_coproduct` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.isoOnAllShifts_cone` (lem-sc-shift-saturated-iso-locus).
- `CategoryTheory.ShiftSaturated.projection_exactStructures` (lem-sc-derived-separate-exact-structures).
- `CategoryTheory.ShiftSaturated.qc_triangulated` (lem-sc-derived-separate-exact-structures).
- `CategoryTheory.ShiftSaturated.rightAdjointTensor_exactStructures` (lem-sc-derived-separate-exact-structures).
- `CategoryTheory.ShiftSaturated.perfectClosure_le_isoOnAllShifts` (lem-sc-perfect-localizing-iso-locus).
- `CategoryTheory.ShiftSaturated.perfect_iso` (lem-sc-perfect-localizing-iso-locus).
- `CategoryTheory.ShiftSaturated.perfect_shift` (lem-sc-perfect-localizing-iso-locus).

The existing application theorems `AlgebraicGeometry.exists_rightAdjointTensorComparison_projection` and `AlgebraicGeometry.smooth_proper_diagonal_tensor_formula` have complete replacement proofs and no direct sorry before or after. Independent second-reader `#print axioms` checks against the current compiled library show that both application theorems, as well as every declaration in the three new helper modules, use only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` remains in those application proofs. The earlier report of inherited holes in these applications was stale. This does not prove the withdrawn assigned statement.

## No longer needed

Removed private imports: `SmoothProperDiagonalTensorFormula` no longer imports `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing`; `RightAdjointTensorComparisonProjection` no longer imports `Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles` or `Mathlib.CategoryTheory.MorphismProperty.Retract`. Both application nodes have proof/proof_deps/proof_origin updated to the actual new route.

The withdrawn closed branch (each node loses only its Lean attachment):

- `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift` — `lem-sc-derived-monoidal-pullback-unital-shift`.
- `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne` — `lem-sc-derived-monoidal-pullback-unital-shift-kflat-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne` — `lem-sc-derived-pullback-canonical-tensor-shift-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization` — `lem-sc-derived-pullback-kflat-cone-counit-normalization`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitShiftAdjustment` — `lem-sc-derived-pullback-kflat-counit-shift-adjustment`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift` — `lem-sc-derived-pullback-tensor-shift`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne` — `lem-sc-derived-pullback-tensor-shift-kflat-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift` — `lem-sc-derived-pullback-tensor-unit-shift`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones` — `lem-sc-derived-pullback-translated-unit-kflat-cones`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles` — `lem-sc-derived-pullback-translated-unit-triangles`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension` — `lem-sc-flat-telescope-bounded-normalization-extension`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent` — `lem-sc-flat-telescope-cone-normalization-descent`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeModelShiftGauge` — `lem-sc-flat-telescope-model-shift-gauge`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationMorphisms` — `lem-sc-flat-telescope-normalization-morphisms`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeShiftGauge` — `lem-sc-flat-telescope-shift-gauge`.
- `Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit` — `lem-sc-derived-pullback-kflat-counit-shift-adjustment-normalized`.
- `Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison` — `lem-sc-normalized-flat-telescope-comparison`.
- `Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeStageComparison` — `lem-sc-normalized-flat-telescope-stage-comparison`.
- `Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison` — `lem-sc-normalized-kflat-representative-comparison`.
- `Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift` — `lem-sc-pinned-projection-counit-exact-shift`.
- `Sheaf.AlgebraicGeometry.ProjectionComparisonExact` — `lem-sc-projection-comparison-exact`.
- `Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles` — `lem-sc-projection-comparison-triangles`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams` — `lem-sc-right-adjoint-tensor-comparison-diagrams`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift` — `lem-sc-right-adjoint-tensor-comparison-shift`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle` — `lem-sc-right-adjoint-tensor-comparison-triangle`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures` — `lem-sc-right-adjoint-tensor-compatible-exact-structures`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing` — `lem-sc-right-adjoint-tensor-locus-localizing`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles` — `lem-sc-right-adjoint-tensor-locus-triangles`.

Complete modules pruned from the targets' source import closure (withdrawals are included; other modules are retained in the repository):

- `Mathlib.CategoryTheory.Limits.MonoCoprod`.
- `Mathlib.Data.Int.Basic`.
- `Sheaf.Algebra.Homology.RelativeBiprodConeExtension` — `lem-sc-relative-biprod-cone-extension`.
- `Sheaf.Algebra.Homology.TensorShiftOneAssociator` — `lem-sc-total-tensor-shift-one-associator`.
- `Sheaf.AlgebraicGeometry.BoundedFlatModelNormalization` — `def-sc-bounded-flat-shift-representative`, `lem-sc-bounded-flat-model-normalization`.
- `Sheaf.AlgebraicGeometry.CompactFlatBarUnionAugmentation` — `lem-sc-compact-flat-bar-union-augmentation`.
- `Sheaf.AlgebraicGeometry.CompactFlatFiniteSubcomplexDiagrams` — `lem-sc-compact-flat-finite-subcomplex-diagrams`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorCover` — `lem-sc-compact-flat-generator-cover`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorRelativeExtension` — `lem-sc-compact-flat-generator-relative-extension`.
- `Sheaf.AlgebraicGeometry.CompactFlatGeneratorTowerResolution` — `lem-sc-compact-flat-generator-tower-resolution`.
- `Sheaf.AlgebraicGeometry.CompactFlatTelescopeBarEnlargement` — `lem-sc-compact-flat-telescope-bar-enlargement`.
- `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift` — `lem-sc-derived-monoidal-pullback-unital-shift`.
- `Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne` — `lem-sc-derived-monoidal-pullback-unital-shift-kflat-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne` — `lem-sc-derived-pullback-canonical-tensor-shift-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization` — `lem-sc-derived-pullback-kflat-cone-counit-normalization`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitAdjustmentFactor` — `lem-sc-derived-pullback-kflat-counit-shift-adjustment-factor`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitData` — `lem-sc-derived-pullback-kflat-counit-data`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitShiftAdjustment` — `lem-sc-derived-pullback-kflat-counit-shift-adjustment`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackShiftedUnitIsoData` — `lem-sc-derived-pullback-shifted-unit-iso-data`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift` — `lem-sc-derived-pullback-tensor-shift`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne` — `lem-sc-derived-pullback-tensor-shift-kflat-one`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift` — `lem-sc-derived-pullback-tensor-unit-shift`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones` — `lem-sc-derived-pullback-translated-unit-kflat-cones`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles` — `lem-sc-derived-pullback-translated-unit-triangles`.
- `Sheaf.AlgebraicGeometry.FlatComparisonPreservesCountableCoproducts` — `lem-sc-flat-comparison-preserves-countable-coproducts`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowBarData` — `lem-sc-flat-telescope-arrow-bar-data`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowCocycles` — `lem-sc-flat-telescope-arrow-cocycles`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeArrowDiagram` — `lem-sc-flat-telescope-arrow-diagram`, `lem-sc-flat-telescope-arrow-diagram-construction`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeBoundedNormalizationExtension` — `lem-sc-flat-telescope-bounded-normalization-extension`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeConeNormalizationDescent` — `lem-sc-flat-telescope-cone-normalization-descent`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeModelShiftGauge` — `lem-sc-flat-telescope-model-shift-gauge`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationIsIso` — `lem-sc-flat-telescope-normalization-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationMorphisms` — `lem-sc-flat-telescope-normalization-morphisms`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeNormalizationUnshiftedIsIso` — `lem-sc-flat-telescope-normalization-unshifted-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopePullbackSumColimit` — `lem-sc-flat-telescope-pullback-sum-colimit`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeShiftGauge` — `lem-sc-flat-telescope-shift-gauge`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap` — `def-sc-flat-telescope-stage-map`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeStageMapRefinement` — `lem-sc-flat-telescope-stage-map-refinement`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeStageNaturality` — `lem-sc-flat-telescope-stage-naturality`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumComparisonIsIso` — `lem-sc-flat-telescope-sum-comparison-is-iso`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeSumModels` — `lem-sc-flat-telescope-sum-models`.
- `Sheaf.AlgebraicGeometry.FlatTelescopeTargetRefinement` — `lem-sc-flat-telescope-target-refinement`.
- `Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation` — `lem-sc-kflat-localized-cone-presentation`.
- `Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit` — `lem-sc-derived-pullback-kflat-counit-shift-adjustment-normalized`.
- `Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison` — `lem-sc-normalized-flat-telescope-comparison`.
- `Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeStageComparison` — `lem-sc-normalized-flat-telescope-stage-comparison`.
- `Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison` — `lem-sc-normalized-kflat-representative-comparison`.
- `Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift` — `lem-sc-pinned-projection-counit-exact-shift`.
- `Sheaf.AlgebraicGeometry.ProjectionComparisonExact` — `lem-sc-projection-comparison-exact`.
- `Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles` — `lem-sc-projection-comparison-triangles`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams` — `lem-sc-right-adjoint-tensor-comparison-diagrams`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift` — `lem-sc-right-adjoint-tensor-comparison-shift`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle` — `lem-sc-right-adjoint-tensor-comparison-triangle`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures` — `lem-sc-right-adjoint-tensor-compatible-exact-structures`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing` — `lem-sc-right-adjoint-tensor-locus-localizing`.
- `Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles` — `lem-sc-right-adjoint-tensor-locus-triangles`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitAssociativity` — `lem-sc-scheme-canonical-shift-unit-associativity`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso` — `def-sc-scheme-canonical-shift-unit-iso`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociator` — `lem-sc-scheme-canonical-tensor-shift-associator`.
- `Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShiftAssociatorKFlatOne` — `lem-sc-scheme-canonical-tensor-shift-associator-kflat-one`.
- `Sheaf.AlgebraicGeometry.SchemeTensorShiftBinaryLocalizationSquare` — `lem-sc-scheme-tensor-shift-binary-localization-square`.
- `Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization` — `aux-sc-target-comparison-isIso`, `aux-sc-target-comparison-second`, `lem-sc-scheme-tensor-shift-localization-normalization`, `aux-sc-target-comparison-first-core`, `aux-sc-target-comparison-first`.
- `Sheaf.CategoryTheory.IntegerShiftFromOne` — `lem-sc-integer-shift-from-one`.
- `Sheaf.CategoryTheory.NatTransFromResolvingClass` — `lem-sc-nattrans-from-resolving-class`.
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`.
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift`.

The earlier unlanded sandbox attempt and all its new hole-bearing split-offs are not part of this delivery. In particular the literal unshifted comparison, relative gauge, normalized cone naturality, presentation-descent and refinement split chain are unnecessary. Their files were removed from the delivered `lean/` and `dag/nodes/` trees, not merely hidden behind another sorry.

## Where the brief, the DAG or earlier work was wrong

The inherited cone-normalization expansion proves much more than invertibility of the root's already constructed natural mate. Completing triangles alone does not supply canonical natural cone maps or presentation-independent normalized morphisms. This audit does not establish the retired cone statement false. Its coherence problem is avoided upstream by the correct five-term diagram, whose fourth and fifth vertical components are transported τ at A[1] and B[1], not the shifts of τ at A and B. Thus no new comparison-normalization theorem is needed. Cutting only the diagonal application would leave the old branch live via `RightAdjointTensorComparisonNatural`; the projection application is therefore cut in the same delivery.

The full blueprint search for “shift saturated” and “exact adjoint” found no matching imported node; “isomorphism locus” found the proper base-change perfect projection formula, whose statement is the application rather than this categorical closure lemma. Mathlib LeanSearch was unavailable (Internal Server Error); LeanFinder/Loogle and source grep were run and recorded for all three new nodes. The appropriate component APIs are used in the actual proofs.

## New nodes

`lem-sc-shift-saturated-iso-locus` records invertibility of a natural comparison on all shifts is localizing. It is fully proved in `Sheaf.CategoryTheory.ShiftSaturatedIsoLocus`; its Lean record also names the related proved API declarations in that module. No further worker obligation or new sorry is introduced.

`lem-sc-derived-separate-exact-structures` records separate exact shift structures for the two tensor comparisons. It is fully proved in `Sheaf.AlgebraicGeometry.DerivedExactStructures`; its Lean record also names the related proved API declarations in that module. No further worker obligation or new sorry is introduced.

`lem-sc-perfect-localizing-iso-locus` records perfect localizing generation detects a natural isomorphism on all shifts. It is fully proved in `Sheaf.AlgebraicGeometry.PerfectLocalizingIsoLocus`; its Lean record also names the related proved API declarations in that module. No further worker obligation or new sorry is introduced.

Change record: `coord/changes/shift-saturated-normalization-pruning.md`.

## Second reading by P3

1. **Statements and visible data — PASS.** Compared every existing delivered module with
   its repository version. The raw signatures of the two changed application theorems
   are byte-for-byte identical, including the arbitrary supplied monoidal structure,
   the specified adjunctions and the pinned inverse equations. Their public imports
   are identical. The two validation clients are byte-for-byte unchanged. The 28
   declaration withdrawals are deliberate and enumerated in `deleted.txt` and
   `coord/changes/shift-saturated-normalization-pruning.md`; they are pruning, not
   weakened replacement statements. No target or target-visible definition changes.
   The local claim snapshot names only P3's assigned item among the existing modules
   changed or withdrawn; all other touched existing modules are unclaimed.

2. **Proof and axioms — PASS.** Independently compiled all seven sandbox modules with
   `lcompile.py --all`, with no errors or warnings. Scanned the delivered sources:
   no sorry and no forbidden axiom, unsafe, opaque, extern or implementation override.
   A separate scratch module printed the axioms of all 13 new API declarations and
   both changed application theorems: each uses only propext, Classical.choice and
   Quot.sound. The five-term chase uses independent invertible maps at the fourth and
   fifth vertices and proves its four squares by naturality. Definitions are concrete;
   no arbitrary witness is chosen from an unproved existence theorem.

3. **New statements and edge cases — PASS, metadata corrected.** There are no new
   hole-bearing split-offs. Checked the generic cone lemma, exact structures and
   perfect-closure reduction against their Lean statements and nodes. Empty
   coproducts are included by the preserved-colimit argument; all integer shifts,
   including negative and zero shifts, use shift-add and shift-zero isomorphisms.
   Perfection shifts both local bounds by subtracting n. Repeated search using
   LeanFinder's “five lemma exact sequence five objects invertible outer four
   morphisms” query and source grep. The upstream Triangulated.Functor and
   Triangulated.Generators results require NatTrans.CommShift, absent here, so do not
   replace this all-shifts argument. QCqsProjectionMateAffineLocus has an applicable
   special-case argument but no reusable generic theorem. Existing private proofs
   of the diagram chase and perfect stability are correctly attributed. Corrected
   the new perfect-localizing node to describe an object property on D_QCoh(X),
   matching the Lean domain, rather than an ambient-category predicate. Added source,
   proof and blueprint docstrings to the new generic closure API declarations.

4. **Top-down pruning and unit route — PASS.** Both application proofs retain the
   existing natural adjunction mate and the perfect case, then apply generation to
   its all-shifts isomorphism locus. The shortest available component APIs are used;
   no comparison-normalization or shift-compatibility obligation is smuggled back in.
   Independently rebuilt the source import graph: no remaining module imports any
   of the 28 withdrawals, and 66 modules (62 Sheaf modules) leave TargetsCheck's
   closure. The two removed proof-dependency nodes are both listed under No longer
   needed. Checked all unit records: none of the 68 nodes attached to pruned modules
   appears in any realized statement or step. The sk-thm-picard-duality unit's
   statement, route, and existing realized fields are unchanged.

5. **DAG agreement — PASS after correction.** Checked every delivered node diff:
   existing withdrawn nodes change only their Lean attachment; the two applications
   change only proof, proof_deps and proof_origin. For every new node and application
   node, proof_deps equals the union of step uses. Each new node's lean.statement is
   verbatim in its module and its creation, source, searches, chapter, unit and
   blueprint ancestry fields are present. The three new nodes describe proved,
   strictly smaller components of the argument and introduce no new obligations.

Second-reading changes: corrected the perfect-localizing node's domain description,
added missing explanatory docstrings to the new generic API, and corrected the stale
axiom-status claim in this report. No mathematical proof or existing signature changed.
