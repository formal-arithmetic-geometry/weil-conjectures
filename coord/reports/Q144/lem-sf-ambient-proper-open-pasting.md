## Worker report

Repair by Q144 of lem-sf-ambient-proper-open-pasting, 2026-10-22. The named sandbox initially contained only .brief markers: no delivered node, report or search log. I recovered the returned ten-step proof from the read-only live node; it has exactly 10148 proof-text characters, matching the return. No git command, repository/launcher edit, Lean edit, compiler or build was run. The delivery tool will rebase the stage-1 fields onto current main and retain its maintainer-owned records.

The parent statement is byte-for-byte unchanged. Its new proof has 2328 characters. The five new nodes below are all status unsplit, mathlib_match null, proof [], proof_deps [], proof_origin null. They are independent future proof tasks, not completed proofs. Generic results remain citations instead of new nodes.

### Files written

- dag/nodes/sec-six-functors/lem-sf-ambient-proper-open-pasting.json: repaired parent split.

- dag/nodes/sec-six-functors/lem-sf-ambient-pullback-tensor-coherence.json: statement, unsplit; no full Mathlib match.

- dag/nodes/sec-six-functors/lem-sf-ambient-adjunction-compositor-normalization.json: statement, unsplit; no full Mathlib match.

- dag/nodes/sec-six-functors/lem-sf-ambient-clopen-restriction-uniqueness.json: statement, unsplit; no full Mathlib match.

- dag/nodes/sec-six-functors/lem-sf-ambient-exact-clopen-comparison-localization.json: statement, unsplit; no full Mathlib match.

- dag/nodes/sec-six-functors/lem-sf-ambient-underived-clopen-pasting.json: statement, unsplit; no full Mathlib match.

- report.md and citations.json; searches.jsonl is written only by msearch.py.

### Attachments

None. Searched the blueprint id and proper/open notions throughout lean/WeilConjectures. The project declaration in lean/Sheaf/SixFunctors/AmbientProperOpenPasting.lean is sorried; its Laws structure and docstring describe the old ten-step argument, but are not finished upstream proofs.

### WANTED

None. All sources used are present locally.

### Fault repaired and remaining work

The returned fault is excessive proof size and insufficient parallel work. Five distinct argument tasks now carry the old proof: Steps 1+3 go to lem-sf-ambient-pullback-tensor-coherence; Step 2 to lem-sf-ambient-adjunction-compositor-normalization; Steps 4+5 to lem-sf-ambient-clopen-restriction-uniqueness; Step 6 to lem-sf-ambient-exact-clopen-comparison-localization; Steps 7+8 and the identity-square calculation in Step 10 to lem-sf-ambient-underived-clopen-pasting. Old Step 9 is the parent localization/mate assembly; the refinement substitution and scope check of old Step 10 remain in the parent. No statement dispute and no route change. Proofs of the five leaves are intentionally left for parallel workers, as the return explicitly requires.

## New nodes

### lem-sf-ambient-pullback-tensor-coherence

Own argument: pullback and tensor/composition normalization (returned Steps 1,3). Source read: literature/stacks-project/sites-modules.tex, Tag 03D3 (lemma-adjoint-push-pull-modules); sites.tex Tag 03CB (lemma-composition-morphisms-sites). Agent extension of the explicit tensor formula and K-flat comparison to both ambient coefficient settings; returned proof Steps 1 and 3.

The statement introduces its own coefficient data, categories, geometry and all maps. It records the needed conclusions and comparison formulas, not proof steps. The old argument for the task is retained verbatim below. Mathlib verdict: no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation.

Searches actually run (query text is preserved exactly):

- grep | pullback_assoc|pullbackComp|leftDerivedUpperStarTensor | 25 hits; Mathlib/CategoryTheory/LocallyCartesianClosed/ExponentiableMorphism.lean, Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean, Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean, Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean, Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean, Mathlib/CategoryTheory/LocallyCartesianClosed/ChosenPullbacksAlong.lean, Mathlib/AlgebraicGeometry/ColimitsOver.lean, Mathlib/AlgebraicGeometry/Sites/Pretopology.lean | no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation

- loogle | SheafOfModules.pullback_assoc | 1 hits; SheafOfModules.pullback_assoc | no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation

- leansearch | Pullback tensor comparison commutes with composition for unbounded derived sheaves of constant finite rings and inverse ring systems | 8 hits; CategoryTheory.Limits.pullback.mapDesc_comp, SheafOfModules.conjugateEquiv_pullbackComp_inv, CategoryTheory.MorphismProperty.Over.pullbackComp_left_fst_fst, AlgebraicGeometry.Scheme.Modules.pullbackComp, CategoryTheory.MorphismProperty.Over.pullbackComp_hom_app_left, CategoryTheory.Limits.pullback.map_comp, SheafOfModules.pullbackComp, CategoryTheory.MorphismProperty.Over.pullbackComp.congr_simp | no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation

- leanfinder | Canonical pullback composition on proetale module sheaves is associative unital and compatible with derived tensor for semilinear coefficient systems | 8 hits; AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity, AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity_assoc, AlgebraicGeometry.Scheme.Modules.pullbackComp, SheafOfModules.pullbackComp, AlgebraicGeometry.Scheme.Modules.pseudofunctor_right_unitality_assoc, AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality_assoc, SheafOfModules.pullback_assoc, SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc | no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation

- grep | lemma pullback_assoc|def pullbackComp|conjugateEquiv_pullbackComp | 3 hits; Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean, Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean | no match: ordinary underived module pullback coherence is present, but not the combined constant-ring section formula, semilinear transition certificate and unbounded derived tensor/composition equation

### lem-sf-ambient-adjunction-compositor-normalization

Own argument: canonical direct-image and open-extension compositors (returned Step 2). Source read: literature/stacks-project/sites-cohomology.tex, Tag 0D6E (lemma-derived-pushforward-composition); derived.tex Tag 09T5 (lemma-derived-adjoint-functors). Agent normalization and threefold-coherence formulation; returned proof Step 2.

The statement introduces its own coefficient data, categories, geometry and all maps. It records the needed conclusions and comparison formulas, not proof steps. The old argument for the task is retained verbatim below. Mathlib verdict: no match: generic adjunction/compositor identities are present, but they do not identify both ambient geometric realizations with their specified resolution and open-localization compositors.

Searches actually run (query text is preserved exactly):

- grep | conjugateEquiv.*comp|pullbackComp|pushforwardComp | 25 hits; Mathlib/CategoryTheory/Adjunction/CompositionIso.lean, Mathlib/CategoryTheory/Adjunction/CompositionIso.lean, Mathlib/CategoryTheory/Adjunction/CompositionIso.lean, Mathlib/CategoryTheory/Adjunction/CompositionIso.lean, Mathlib/CategoryTheory/Adjunction/CompositionIso.lean, Mathlib/CategoryTheory/Adjunction/Mates.lean, Mathlib/CategoryTheory/Adjunction/Mates.lean, Mathlib/CategoryTheory/Adjunction/Mates.lean | no match: generic adjunction/compositor identities are present, but they do not identify both ambient geometric realizations with their specified resolution and open-localization compositors

- loogle | CategoryTheory.Adjunction.comp | 12 hits; CategoryTheory.Adjunction.comp, CategoryTheory.Equivalence.trans_toAdjunction, CategoryTheory.Adjunction.comp_homEquiv, CategoryTheory.Adjunction.comp_counit_app, CategoryTheory.Adjunction.comp_unit_app, CategoryTheory.Adjunction.comp_counit_app_assoc, CategoryTheory.Adjunction.comp_unit_app_assoc, CategoryTheory.Adjunction.comp_counit | no match: generic adjunction/compositor identities are present, but they do not identify both ambient geometric realizations with their specified resolution and open-localization compositors

- leansearch | Unbounded derived pushforward composition preserves the composite adjunction units counits and open extension composition | 8 hits; CategoryTheory.Adjunction.derivedη.congr_simp, CategoryTheory.Adjunction.derived_unit, SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app, CategoryTheory.Adjunction.comp_unit_app, SheafOfModules.pushforwardPushforwardAdj, CategoryTheory.Under.postAdjunctionRight_unit_app_right, CategoryTheory.ExponentiableMorphism.pushforwardComp, SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app | no match: generic adjunction/compositor identities are present, but they do not identify both ambient geometric realizations with their specified resolution and open-localization compositors

- leanfinder | Canonical derived direct image and open extension compositors are associative unital conjugates of inverse image composition in proetale ringed diagram topoi | 8 hits; AlgebraicGeometry.Scheme.IsLocallyDirected.homOfLE_tAux_assoc, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.invApp_app_assoc, AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity, AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app_assoc, AlgebraicGeometry.PresheafedSpace.map_comp_c_app, AlgebraicGeometry.LocallyRingedSpace.comp_c, AlgebraicGeometry.Scheme.IsLocallyDirected.homOfLE_tAux, AlgebraicGeometry.SheafedSpace.IsOpenImmersion.invApp_app_assoc | no match: generic adjunction/compositor identities are present, but they do not identify both ambient geometric realizations with their specified resolution and open-localization compositors

### lem-sf-ambient-clopen-restriction-uniqueness

Own argument: proper/open clopen factor and restriction uniqueness (returned Steps 4,5). Source read: literature/stacks-project/more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open), open-square geometry; sites.tex Tag 04TS (lemma-mapping-property-glue), disjoint-open gluing. Agent clopen Hom-bijection formulation for ambient pro-etale modules and systems; returned proof Steps 4 and 5.

The statement introduces its own coefficient data, categories, geometry and all maps. It records the needed conclusions and comparison formulas, not proof steps. The old argument for the task is retained verbatim below. Mathlib verdict: no match: open/proper stability and sheaf extensionality are present, but not this proper/open factorization together with the clopen Hom bijection for both pro-etale coefficient categories.

Searches actually run (query text is preserved exactly):

- grep | clopen|IsClosedImmersion.*IsOpenImmersion|IsOpenImmersion.*IsClosedImmersion | 6 hits; Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean, Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean, Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean, Mathlib/AlgebraicGeometry/Morphisms/QuasiFinite.lean, Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean, Mathlib/AlgebraicGeometry/Morphisms/OpenImmersion.lean | no match: open/proper stability and sheaf extensionality are present, but not this proper/open factorization together with the clopen Hom bijection for both pro-etale coefficient categories

- leansearch | Proper open square induced map to fiber product is clopen and morphisms into its extension by zero are determined by restriction | 8 hits; AlgebraicGeometry.IsProper.instMorphismRestrict, TrivSqZeroExt.instTopologicalSpace, AlgebraicGeometry.Scheme.instIsOpenImmersionF, Opens.mayerVietorisSquare, Opens.mayerVietorisSquare', AlgebraicGeometry.IsOpenImmersion.instπWalkingCospanSchemeCospanOne, Opens.mayerVietorisSquare'_toSquare, AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict | no match: open/proper stability and sheaf extensionality are present, but not this proper/open factorization together with the clopen Hom bijection for both pro-etale coefficient categories

- loogle | AlgebraicGeometry.IsOpenImmersion | 12 hits; AlgebraicGeometry.isOpenImmersion_isMultiplicative, AlgebraicGeometry.isOpenImmersion_isStableUnderComposition, AlgebraicGeometry.isOpenImmersion_respectsIso, AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange, AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.IsOpenImmersion.instHasOfPostcompPropertyScheme, AlgebraicGeometry.Scheme.Hom.opensRange, AlgebraicGeometry.IsOpenImmersion.mono | no match: open/proper stability and sheaf extensionality are present, but not this proper/open factorization together with the clopen Hom bijection for both pro-etale coefficient categories

- leanfinder | Clopen decomposition of proetale module sheaves and semilinear systems determines maps into extension by zero uniquely by restriction | 8 hits; SheafOfModules.Presentation.map_π_eq, AlgebraicGeometry.Scheme.Modules.hom_ext, AlgebraicGeometry.Scheme.Modules.hom_ext_iff, SheafOfModules.generatorsOfIsCokernelFree_π, ModuleCat.Tilde.res_const, PresheafOfModules.Sheafify.instUniqueSMulCandidate, PresheafOfModules.Sheafify.SMulCandidate.mk.inj, SheafOfModules.freeHomEquiv | no match: open/proper stability and sheaf extensionality are present, but not this proper/open factorization together with the clopen Hom bijection for both pro-etale coefficient categories

### lem-sf-ambient-exact-clopen-comparison-localization

Own argument: intrinsic clopen comparison agrees with exact localization and its specified mate (returned Step 6). Source read: literature/stacks-project/more-etale.tex, Tag 0F7B (lemma-shriek-proper-and-open), map normalization; sites-cohomology.tex Tag 07A7 (remark-base-change), adjunction transpose. Agent exact-localization comparison for the stated ambient categories; returned proof Step 6.

The statement introduces its own coefficient data, categories, geometry and all maps. It records the needed conclusions and comparison formulas, not proof steps. The old argument for the task is retained verbatim below. Mathlib verdict: no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories.

Searches actually run (query text is preserved exactly):

- grep | extension.*zero|lowerShriek|LowerShriek|clopen | 0 hits;  | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

- loogle | CategoryTheory.Adjunction, CategoryTheory.Localization | 0 hits; . loogle: unknown identifier 'CategoryTheory.Localization' | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

- leansearch | Localization of extension by zero base change preserves adjunction unit and clopen projection normalization for module systems | 8 hits; CategoryTheory.Adjunction.localization_unit_app, CategoryTheory.Adjunction.localization, isLocalizedModule_iff_isBaseChange, CategoryTheory.Adjunction.Localization.η, instIsLocalizedModuleFinsuppLinearMap, IsLocalizedModule.isBaseChange, Algebra.Extension.localization, IsLocalizedModule.recOn | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

- leanfinder | Exact proper open clopen projection comparison localizes to the canonical open base change map in unbounded derived proetale system categories | 8 hits; LightProfinite.proj_comp_transitionMapLE, LightProfinite.proj_comp_transitionMap, LightProfinite.proj_comp_transitionMapLE', LightProfinite.proj_comp_transitionMap', Condensed.isColimitLocallyConstantPresheaf_desc_apply, Profinite.NobelingProof.CC_exact, LightCondensed.isColimitLocallyConstantPresheaf_desc_apply, LightCondensed.isColimitLocallyConstantPresheafDiagram_desc_apply | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

- loogle | CategoryTheory.Adjunction.localization | 3 hits; CategoryTheory.Adjunction.localization, CategoryTheory.Adjunction.localization_counit_app, CategoryTheory.Adjunction.localization_unit_app | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

- grep | localization_unit_app|def localization|def comp|theorem mateEquiv_vcomp | 25 hits; Mathlib/CategoryTheory/PathCategory/Basic.lean, Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean, Mathlib/CategoryTheory/FiberedCategory/BasedCategory.lean, Mathlib/CategoryTheory/FiberedCategory/Grothendieck.lean, Mathlib/CategoryTheory/Endofunctor/Algebra.lean, Mathlib/CategoryTheory/Endofunctor/Algebra.lean, Mathlib/CategoryTheory/Square.lean, Mathlib/CategoryTheory/Localization/LocalizerMorphism.lean | no match: generic localization preserves adjunctions, but does not construct or identify this intrinsic geometric clopen arrow in both coefficient categories

### lem-sf-ambient-underived-clopen-pasting

Own argument: vertical/horizontal intrinsic clopen pasting and identity squares before deriving (returned Steps 7,8,10). Source read: literature/stacks-project/more-etale.tex, Tags 0F7C (lemma-shriek-proper-and-open-compose) and 0F7D (lemma-shriek-proper-and-open-compose-horizontal). Agent underived clopen-restriction formulation on pro-etale modules and semilinear systems; returned proof Steps 7 and 8 and identity part of Step 10.

The statement introduces its own coefficient data, categories, geometry and all maps. It records the needed conclusions and comparison formulas, not proof steps. The old argument for the task is retained verbatim below. Mathlib verdict: no match: generic mate pasting does not prove the underived intrinsic clopen arrows have identity restrictions and coincide with the outer geometric arrow.

Searches actually run (query text is preserved exactly):

- grep | proper.*open.*past|properOpen|shriek.*comp | 0 hits;  | no match: generic mate pasting does not prove the underived intrinsic clopen arrows have identity restrictions and coincide with the outer geometric arrow

- loogle | CategoryTheory.mateEquiv_vcomp | 1 hits; CategoryTheory.mateEquiv_vcomp | no match: generic mate pasting does not prove the underived intrinsic clopen arrows have identity restrictions and coincide with the outer geometric arrow

- leansearch | Extension by zero clopen projection base change natural transformations paste before deriving on inverse systems of module sheaves | 8 hits; CategoryTheory.GrothendieckTopology.diagramNatTrans_zero, CategoryTheory.Functor.toRightDerivedZero, CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_zero, PresheafOfModules.instZeroHom, CategoryTheory.instZeroHomSheaf, CategoryTheory.Functor.leftDerivedZeroIsoSelf_inv_hom_id, AlgebraicGeometry.Scheme.Modules.Hom.zero_app, CategoryTheory.coherentTopology.isLocallySurjective_π_app_zero_of_isLocallySurjective_map | no match: generic mate pasting does not prove the underived intrinsic clopen arrows have identity restrictions and coincide with the outer geometric arrow

- leanfinder | Underived proper open clopen projection comparisons of sheaves and semilinear systems obey horizontal and vertical pasting | 8 hits; SheafOfModules.Presentation.map_π_eq, TopCat.Sheaf.objSupIsoProdEqLocus_inv_snd, TopCat.Sheaf.objSupIsoProdEqLocus_inv_fst, TopCat.Sheaf.objSupIsoProdEqLocus_inv_eq_iff, AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app', TopCat.Sheaf.objSupIsoProdEqLocus_hom_snd, TopCat.Sheaf.objSupIsoProdEqLocus_hom_fst, AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app | no match: generic mate pasting does not prove the underived intrinsic clopen arrows have identity restrictions and coincide with the outer geometric arrow

## Not duplicates

Searched the entire DAG by tags and title/statement keywords, and the whole blueprint with tools/blueprint_refs.py search (tensor composition, adjunction, clopen, proper-open), plus ancestor. No blueprint node states any full extracted claim. The new nodes serve the existing ancestor sentence on composition/refinement coherence. The system-only neighbors and the ordinary etale boundedness-dependent comparisons are distinguished explicitly below. Each new node also differs from the parent: it is one proper subargument, never the whole ambient pasting theorem.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-single-coefficient-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition of restricted single-complex coefficient maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-composition-law: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition law for restricted single transitions.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-underived-ringed-operations-linear: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compatible global scalars on the underived ringed pro-etale adjoint pair.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-abelian-raw-pullback-coherence-extend: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Cocone extension of raw pullback coherence.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-unit-lift: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Lift a restricted coefficient unit to its single complex.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-abelian-raw-pullback-coherence: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Coherent natural raw pullbacks for varying abelian coefficients.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-abelian-raw-pullback-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition of varying-coefficient raw pullbacks.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-transition-laws: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Unit and composition laws for the explicit restricted transitions.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-cone-naturality: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Naturality of the explicit restricted cone comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-sc-etale-module-set-pullback-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical module-to-set etale inverse-image comparison.

lem-sf-ambient-pullback-tensor-coherence vs def-sbc-raw-module-abelian-hom-map: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The explicit scalar-forgetting map of raw derived Hom.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-raw-affine-complex-system-map-coherence: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity, composition and cone equations of canonical complex cohomology maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-raw-module-free-source-hom-bijective: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Explicit underived free-source comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-cone-leg: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compatibility of the explicit restricted cone comparison with colimit legs.

lem-sf-ambient-pullback-tensor-coherence vs def-sbc-raw-module-scalar-pullback-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical scalar forgetting and inverse-image comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-restricted-affine-single-identity-law: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity law for restricted single transitions.

lem-sf-ambient-pullback-tensor-coherence vs def-sbc-restricted-affine-single-maps: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Explicit restricted single-complex transitions and cone comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-raw-triangle-pullback-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Raw triangle pullback composition with arbitrary derived coefficient maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-abelian-raw-pullback-identity: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity of varying-coefficient raw pullback.

lem-sf-ambient-pullback-tensor-coherence vs lem-sbc-abelian-raw-pullback-coherence-base: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Base coherence of raw pullbacks.

lem-sf-ambient-pullback-tensor-coherence vs lem-sf-proetale-tensor-composition-unit: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The explicit pro-etale tensor pullback comparison preserves composite adjunction units.

lem-sf-ambient-pullback-tensor-coherence vs lem-trf-site-inverse-image-composition-generators: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition of sheaf inverse images on nested colimit generators.

lem-sf-ambient-pullback-tensor-coherence vs lem-zl-module-terminal-scalar-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Normalized module evaluation compares scalar-extension adjoints.

lem-sf-ambient-pullback-tensor-coherence vs lem-trf-constant-coefficient-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical pro-etale constant coefficient maps respect composition.

lem-sf-ambient-pullback-tensor-coherence vs def-sfb-proetale-unit-normalized-adjunction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Unit-normalized adjunction for pro-etale module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs def-a1-integral-completed-tower-pullback-universes: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Integral completed strict-tower interfaces at independent universes.

lem-sf-ambient-pullback-tensor-coherence vs def-a1-integral-finite-pullback-tower: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Strict integral finite-coefficient pullback tower.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-strict-local-module-sections-set-equiv: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical module/set equivalence of strict-local terminal sections.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-section-comparison-laws: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Coherence of canonical etale section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-sets-sheaf-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Sheaf-level unit and composition comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-square-iso-pasting: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity and pasting laws of the sheaf-level square isomorphism.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-strict-quotient-scalar-direct-isomorphisms: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Invertibility of the normalized ordinary and strict scalar right mates.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-terminal-cone: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Terminal section transport commutes with a diagonal cone map.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-sections-iso-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Coefficient and terminal section transport along any scheme isomorphism.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-flat-restriction-derived-mate: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns FlatRestrictionDerivedMate.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-inverse-image-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Inverse images along a composite: the canonical isomorphism compatible with the units.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-model-ring-presentation: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The transported pro-etale ring unit presents set inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-inverse-image-action-adjunction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Underlying inverse image for modules from a normalized ring presentation.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-fpqc-matching-sections-pullback: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Matching global sections remain equal along any cone.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-coefficient-product-composition-component: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition calculation at one outgoing-arrow factor.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-module-ring-iso-adjunction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Transport a linearity criterion across a ring-sheaf isomorphism.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-global-section-square: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Global inverse-image sections respect a commutative square.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-derived-module-underlying-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Derived coefficient-forgetting comparisons respect restriction.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-open-square-diagram-identity: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity coefficient law across a diagram of commuting restriction squares.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-affine-etale-restriction-composition-mates: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Unit-preserving affine composition mates and restriction coherence.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-inverse-image-module-linear-criterion: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Linearity is preserved and reflected by the etale abelian adjunction.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-coefficient-product-transition-laws: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity and composition laws for explicitly constructed outgoing-arrow product transitions.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-etale-set-constant-pullback-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Constant comparison for constructed etale inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-geometric-module-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Restriction of the underlying adjunction to linear maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-coefficient-product-identity-component: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity calculation at one outgoing-arrow factor.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-fpqc-agreement-sections-overlap: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The two canonical equality predicates coincide on a double overlap.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-module-inverse-image-action: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Scalar actions on the constructed abelian inverse image.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-sets-terminal-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Terminal section transport for a triangle of schemes.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-sets-terminal-restriction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Terminal inverse-image restriction for an etale object.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-module-pullback-forget-naturality: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Naturality of etale module pullback under forgetting coefficients.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-terminal-transition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Terminal section identifications commute with etale transitions.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-sites-and-cohomology: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Sites, morphisms of sites and cohomology on an object of a site.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-constant-module-pullback-encoding: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Restriction to constant scalars commutes with canonical pullback.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-inverse-image-module-counit-linear-lift: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The transported abelian counit lifts to a module map.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-ring-restriction-pullback-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical restriction-of-scalars and identified-coefficient pullback comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lemma-weil-pbc-etale-pullback-forget-modules: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Étale pullback commutes with forgetting constant-ring module coefficients.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-module-inverse-image-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Transport of the module lift along a constant-ring comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-section-comparison-equal-open: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Agreement open for canonical etale inverse-image section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-mayer-vietoris-module-exact-segment: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Exact Mayer--Vietoris segment for module-sheaf pullbacks.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-mayer-vietoris-module-vanishing: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Two-open Mayer--Vietoris vanishing for inverse images of module sheaves.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-affine-etale-restriction-composition-gamma: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Affine base-change composition lifts through full affine inclusion.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-cartesian-unit-equality: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Equality of unit sections on a cartesian etale object.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-strict-local-module-sections-set-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Representative compatibility of strict-local coefficient and symmetry transport.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-site-system-finite-coverings: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Finite covering transport across evaluation equivalences.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-set-constant-transport-generators: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compositional transport on constant generators.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-site-morphism-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition of morphisms of sites (Stacks 03CB).

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-section-comparison-naturality: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Restriction naturality of canonical section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-abelian-underived-exchange: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Coefficient forgetting respects underived exchange.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-inverse-image-unit-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Underlying module inverse-image comparison compatible with the unit.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-section-comparison-identity: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity for a canonical etale section comparison.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-direct-image-composition-coherence: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Associativity and unit laws of the composition isomorphisms of direct images.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-flat-ringed-diagram-adjuncts: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Normalized coefficient comparison with adjunct compatibility.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-constant-pullback-identity-coherence: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns ConstantPullbackIdentityCoherence.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-flat-ringed-diagram-input: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compatible flat coefficient input and its module diagram functors.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-module-specialization-unit: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Module unit on an affine weakly contractible closed specialization neighbourhood.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-pullback-section-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Underlying sets of module pullback section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-affine-local-acyclic-open-restriction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Affine-local acyclicity is inherited by open restriction.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-compatible-pullback-sheaf-system: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compatible pullback sheaves form a system and become constant on a cone.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-affine-etale-restriction-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition coherence of unit-preserving affine etale restriction comparisons.

lem-sf-ambient-pullback-tensor-coherence vs def-weil-pbc-flat-ringed-diagram-comparisons: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Comparison functors and localization factors for flat coefficient restriction.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-flat-ringed-diagram-restriction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Flat coefficient restriction and normalized derived operations on module diagrams.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-etale-inverse-image-composition-units: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition isomorphisms of etale inverse images of sheaves of sets, with units.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-constant-pullback-composition-coherence: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns ConstantPullbackCompositionCoherence.

lem-sf-ambient-pullback-tensor-coherence vs new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical unit comparison for module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-set-constant-transport-identity: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identity transport of arbitrary constant-sheaf maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-abelian-inverse-image-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical module-to-abelian inverse-image comparison is invertible.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-unit-section-restriction-comp: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Functoriality of unit restriction along an arbitrary étale lift.

lem-sf-ambient-pullback-tensor-coherence vs new-strict-henselian-stalk-sections-comparison-functor: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Same-universe abelian etale inverse-image adjunction.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-local-stage-image-equations: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns EtaleSetLocalStageImageEquations.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-directed-etale-section-identifications: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Identification of section comparisons on an etale upper tail.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-module-inverse-image-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Underlying sheaves and scalar graph of pro-etale module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-module-inverse-image-underlying: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Underlying abelian sheaf of the pro-etale module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-abelian-pullback-global-sections-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Abelian inverse-image global sections and set section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs new-lem-weil-pbc-proetale-module-canonical-unit: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical adjunction unit comparison for module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-module-inverse-image-action-of-presentations: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Constructing an inverse-image module action from two unit presentations.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-sets-section-comparison-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition for canonical etale section comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-limit-scalar-section-map-laws: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Coherence of descended scalar section maps.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-site-system-finite-sheaf-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Continuity and exact sheaf pullbacks for finite coverings.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-etale-coefficient-product-embedding-compatibility: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Compatibility of explicit product embeddings with the coefficient transitions.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-inverse-image-module-adjunction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Inverse image of modules is left adjoint to direct image (etale sites).

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-flat-restriction-ordinary-comparisons: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns FlatRestrictionOrdinaryComparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-proetale-module-inverse-image-scalar-graph: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Scalar graph compatibility of pro-etale module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-inverse-image-module-unit-linear-lift: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns The transported abelian unit lifts to a module map.

lem-sf-ambient-pullback-tensor-coherence vs lem-cbc-comparison-matching-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Matching families give the fpqc compatibility equation.

lem-sf-ambient-pullback-tensor-coherence vs lem-exc-proetale-finite-module-underlying: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Unit-normalized abelian comparison for finite-ring module inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-pur-independent-module-adjunction: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Module adjunction for an independently sized algebraic inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-pur-support-pair-composition: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Composition coherence for adjoint restriction-kernel diagrams.

lem-sf-ambient-pullback-tensor-coherence vs lem-exc-proetale-finite-scalar-unit-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Finite scalar restriction and pro-etale adjunction units.

lem-sf-ambient-pullback-tensor-coherence vs lem-sp-level-pullback-exact: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Exactness of finite-level inverse image.

lem-sf-ambient-pullback-tensor-coherence vs lem-cbc-extension-zero-perfect-model-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Transport a single local completed constant model across open extension by zero.

lem-sf-ambient-pullback-tensor-coherence vs lem-pur-site-algebraic-composition-unit: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Algebraic transport of unit-normalized site composition and identity.

lem-sf-ambient-pullback-tensor-coherence vs def-pur-integral-finite-pullback: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Finite coefficient module pullback and its canonical generators.

lem-sf-ambient-pullback-tensor-coherence vs lem-sf-ring-sheaf-base-change-mates: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical open and closed base-change mates for arbitrary ring sheaves.

lem-sf-ambient-pullback-tensor-coherence vs def-sp-et-proet-coefficient-transport: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Fixed presentation transport of the recorded intrinsic reduction comparison.

lem-sf-ambient-pullback-tensor-coherence vs def-sp-reduction-direct-image-comparison: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Canonical compact-support coefficient comparison and normalized open coordinates.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-pullback-finite-locally-constant: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Pullback of a finite locally constant etale sheaf.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-derived-unit-leray-id: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Derived unit and Leray identity.

lem-sf-ambient-pullback-tensor-coherence vs lem-weil-pbc-derived-unit-leray-comp: The new claim is the explicit ordinary-and-system module compositor certificate together with K-flat derived tensor/composition coherence; the existing claim concerns Derived unit and Leray composition.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-enriched-sequence-projection-formula: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Uncurried finite projections of the enriched sequence adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-derived-tower-counit-projections: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived constant/limit adjunction with its actual projection counit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-sequence-sections-limit-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived sections and total limit with specified projections.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sf-ringed-restriction-exchange-open-descent: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized ringed restriction exchange and open descent.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-sequence-pushforward-limit-projections: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Restricted total-limit comparison with adjunction projections.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-dg-derived-quillen-calculus: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Enhanced derived adjunction and monoidal Quillen calculus.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-sequence-global-sections-evaluation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived termwise global sections with finite evaluation and transition normalization.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-restricted-tower-resolution-acyclicity: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Acyclicity and projection equations for a restricted varying-ring resolution.

lem-sf-ambient-adjunction-compositor-normalization vs lem-coef-derived-sections-scalar-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Coherent unit-normalized scalar comparison for unbounded derived global sections.

lem-sf-ambient-adjunction-compositor-normalization vs lem-trf-continuous-cocontinuous-derived-shriek: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Unbounded derived lower shriek for continuous and cocontinuous site functors.

lem-sf-ambient-adjunction-compositor-normalization vs def-trf-completion-unit-models: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Ordinary quotient adjunction and normalized derived completion models.

lem-sf-ambient-adjunction-compositor-normalization vs lem-trf-point-reduction-unit-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Point coefficient-reduction comparisons are normalized by scalar-extension units.

lem-sf-ambient-adjunction-compositor-normalization vs lem-trf-completion-unit-canonical-models: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Compatible ordinary and derived presentations of the coefficient adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs def-trf-point-reduction-units: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical scalar-extension units and exact restriction/sections identity at a point.

lem-sf-ambient-adjunction-compositor-normalization vs def-trf-coefficient-tower-operations: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Coefficient tower operations and point sections.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pc-derived-adjoint-functors: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived functors of adjoint functors are adjoint.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pc-derived-base-change-unit-compatibility: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived mate compatibility with the right-derived unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sc-sheaf-algebra-derived-hom-adjunction-map: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived scalar restriction mapDerivedCategory adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs new-everywhere-defined-derived-functors: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Everywhere-defined derived functors.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pc-derived-adjunction-normalization-unique: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Uniqueness of an adjunction with a fixed representative Hom formula.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sc-sheaf-algebra-derived-hom-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns The constructed algebra-valued derived Hom adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs new-derived-adjunction-compatibility: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Compatibility of the derived adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pc-original-counit-adjunction-transport: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Original-counit transport of the normalized scheme pullback adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-derived-cokernel-adjoint-exchange: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Exact exchange for derived cokernel adjunctions.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-finite-principal-support-unit-assembly: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Finite principal-support vanishing assembles the specified derived open unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-internal-scalar-mate-projection: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Restriction of an internal coefficient mate is the specified projection map.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-proper-open-tower-single-unit-formula: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Single derived-unit formula in a proper/open tower.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-proper-open-tower-successive-unit-formula: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Successive derived-unit formula in a proper/open tower.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-normalized-scalar-boundary-naturality: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Naturality of normalized scalar reduction boundaries.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-hypercover-derived-unit-chain-squares: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived-unit representatives and cross-site hypercover chain squares.

lem-sf-ambient-adjunction-compositor-normalization vs def-sfb-identity-open-pullback-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Specified identity-open inverse pullback compositor.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-proper-open-tower-derived-unit: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived-unit resolution calculation in a proper/open tower.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-ringed-comparison-tensor-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Tensor and adjunction compatibility of canonical ringed-topos path comparisons.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-derived-section-scalar-transport: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Localization transport of the normalized scalar adjunction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-exact-compactification-unit-refinement: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized exact compactification units respect canonical refinements.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-integral-quotient-direct-image-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Unbounded quotient-scalar refinement of integral direct image.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-exact-compactification-unit-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Composition of normalized exact compact-support units.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-galois-coefficient-path-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Coherent ringed paths for Galois coefficient restriction.

lem-sf-ambient-adjunction-compositor-normalization vs def-sfb-ringed-derived-comparison-data: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Data of normalized derived monoidal comparisons of ringed topoi.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-integral-quotient-section-mate-realization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Integral quotient scalar and geometric mate realization in section modules.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-scalar-adjunction-unit-coefficient-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized scalar adjunction on K-flat models and the coefficient unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-identity-open-derived-adjunction-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns K-injective normalization and derived adjunction at an identity open locus.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-ringed-kunneth-factorizations: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Two factorizations of the ringed-topos external product comparison.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-ringed-derived-composition-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Composition comparison with normalized representative formulas.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-scalar-change-direct-image-unit: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Internal/sectionwise normalization of the scalar-change direct-image unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-resolving-derived-adjunction-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived adjunction normalized by a left resolving class and K-injectives.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-ringed-derived-identity-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Identity comparison with normalized representative formulas.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-derived-composition-adjunction-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived composition preserves the specified adjunction normalization.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sfb-ringed-derived-monoidal-comparisons: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Monoidal and adjunction normalization of derived ringed-topos comparisons.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-ordinary-ringed-exchange-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Identity and pasting for ordinary ambient ringed exchange.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-ringed-topoi-derived-pushforward-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical composition comparison for unbounded ringed-topos direct images.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-exact-square-derived-counit: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Counits in an exact square from normalization on K-injectives.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-ring-sheaf-change-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived adjunctions under compatible changes of ring sheaves.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-derived-module-scalar-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived scalar restriction for ordinary modules has a left adjoint.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-ringed-derived-adjunction-independent-universes: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived module inverse image is left adjoint to a supplied derived direct image.

lem-sf-ambient-adjunction-compositor-normalization vs def-weil-pbc-derived-direct-image-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Composition isomorphisms of derived direct images (conjugates of those of inverse images).

lem-sf-ambient-adjunction-compositor-normalization vs prop-weil-pbc-derived-inverse-image-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived adjunction of inverse and direct image on D^+.

lem-sf-ambient-adjunction-compositor-normalization vs def-weil-pbc-adjunction-conjugate: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Conjugate transformations of adjoint functors.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-raw-restricted-resolution-naturality: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Raw evaluation is natural on a prescribed injective resolution.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-ring-sheaf-change-adjunction-existence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Existence of the normalized derived direct-image comparison.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-raw-restricted-resolution-restriction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Etale cohomology pullback on a chosen resolution.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-frobenius-exchange-restriction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Finite-level exchange is the restricted ambient exchange.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-pbc-raw-restricted-resolution-class: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Raw resolution evaluation has the canonical cocycle class.

lem-sf-ambient-adjunction-compositor-normalization vs lem-asd-proper-finite-coefficient-extension-core: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Unbounded proper coefficient comparison and restricted projection identity.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-transition-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived semilinear transitions compose.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-coefficient-projection-cocycle: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Coefficient projection cocycle for ordinary derived ringed diagrams.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-coefficient-derived-presentation-exists: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Existence of a normalized derived coefficient presentation.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-extension-evaluation-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Evaluation comparison for derived left extensions.

lem-sf-ambient-adjunction-compositor-normalization vs def-pur-sequence-adjoint-resolution-data: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Resolution data for the coefficient sequence projection.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-sheaf-ring-derived-coefficient-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived change of rings along a map of ring sheaves is left adjoint to restriction of scalars, with normalized unit and transposes.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-resolving-class-derived-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized derived adjunction from a resolving class.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-cochain-adjunction-compatibility: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized derived Hom formulas on cochain complexes.

lem-sf-ambient-adjunction-compositor-normalization vs lem-cbc-cochain-augmentation-descent: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Descent of an augmentation through its universal cochain counit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-transition-unit: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Identity transitions and the canonical derived tensor unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sp-restriction-transition-transpose: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Scalar-adjunction transpose of a compact-support mixed-coefficient map.

lem-sf-ambient-adjunction-compositor-normalization vs lem-cbc-strict-tower-direct-image-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Coherence of canonical strict-tower direct image and its square mates.

lem-sf-ambient-adjunction-compositor-normalization vs lem-kun-module-abelian-kinjective-direct-image-acyclic: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Abelian direct-image acyclicity of a module K-injective complex.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-completed-coefficient-site-data: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Exact scalar restrictions, strict-system restriction and derived limit on one site.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-pushforward-restriction-transition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Restriction-form transition of simultaneous derived direct image.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sf-compact-support-restriction-of-scalars: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Finite-level compact-support direct image commutes with restriction of scalars.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-subsequence-evaluation-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Subsequence evaluation respects restriction composition.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical composition of derived subsequence extensions.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-completed-coefficient-structure-map: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Unique completed coefficient structural map from finite projections.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-algebra-diagram-evaluation-adjunction-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Evaluation of a cartesian algebra-diagram adjunction respects counits and coefficient restriction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-sequence-adjoint-resolution-shifts: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Resolution-normalized identification of the sequence-site derived adjoints.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-derived-composition-cocycle: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Cocycle and identity laws for normalized ringed-topos derived composition.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-cochain-homotopy-derived-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Comparison through the homotopy quotient.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-coefficient-restriction-counit: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived ringed-topos counit under coefficient restriction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-composition-evaluation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Evaluation of the derived subsequence compositor.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-evaluation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived evaluation of the subsequence left extension.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-single-derived-evaluation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived singleton evaluation below and above the input level.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-subsequence-transition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Subsequence evaluation respects derived transitions.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-exact-restriction-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Exact restriction compositors and their localization formulas.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-proetale-direct-image-global-evaluation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized derived global sections after pro-etale direct image.

lem-sf-ambient-adjunction-compositor-normalization vs lem-cbc-etale-derived-direct-image-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Ordinary etale derived direct-image composition and its coherence.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-derived-mate-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Cochain representative formula for normalized derived mates.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-completed-coefficient-direct-image-diagrams: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized completed-coefficient direct image on strict diagrams.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-global-hom-evaluation-model: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns A-linear evaluation-normalized global derived Hom model.

lem-sf-ambient-adjunction-compositor-normalization vs lem-kun-etale-module-abelian-ringed-presentation: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Simultaneous ringed presentations of coefficient forgetting and abelian etale direct image.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-diagram-ring-restriction-pushforward: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived coefficient restriction on ringed diagram topoi.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-ringed-tower-pushforward-limit-acyclic: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Inverse-limit acyclicity of levelwise pushforward of a K-injective tower.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-perfect-quotient-exchange-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Perfect quotient coefficient exchange with augmentation and completion-unit normalization.

lem-sf-ambient-adjunction-compositor-normalization vs def-pur-completed-pushforward-models: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized models for completed-coefficient direct image.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-transition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Localization of actual semilinear transitions.

lem-sf-ambient-adjunction-compositor-normalization vs lem-asd-derived-counit-k-injective-termwise: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived counit on a K-injective representative.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-normalized-adjunction-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Composition and uniqueness of normalized adjunction formulas.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-sheaf-ring-derived-hom-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Compatibility of the derived scalar-extension adjunction with homotopy Hom representatives.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-evaluation-scalar-restriction-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Scalar restriction normalizes the singleton direct-image evaluation comparison.

lem-sf-ambient-adjunction-compositor-normalization vs lem-asd-proper-finite-coefficient-extension: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical unbounded proper direct-image comparison for finite coefficient extension.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-evaluation-transition-mate: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Iterated Hom formula for the transition mate.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-adjunction-transition-coherence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Transition coherence for evaluation mates.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-single-derived-extension: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Deriving the ordinary singleton extension.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-scalar-derived-extension: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns A scalar model as normalized derived extension data.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-extension: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Deriving the ordinary subsequence extension.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-adjunction-mate-transpose: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Transpose formula for a general mate square.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-adjunction-evaluation-composition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Evaluation and composition of normalized adjunction mates.

lem-sf-ambient-adjunction-compositor-normalization vs def-pur-ringed-coefficient-change-presentations: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized coefficient changes between counit presentations.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-coefficient-change-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized coefficient changes and their naturality.

lem-sf-ambient-adjunction-compositor-normalization vs lem-weil-proetale-direct-image-restriction-of-scalars: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Derived pro-etale direct image commutes with restriction of scalars.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-comparison-unit-injective-model: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Injective-resolution representative of the derived etale/pro-etale comparison unit.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-ringed-triple-resolution-formulas: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Common-resolution formulas for two triple direct-image paths.

lem-sf-ambient-adjunction-compositor-normalization vs def-pur-ringed-coefficient-counit-presentations: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized ringed coefficient counit presentations.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-evaluation-index: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Reindexing the selected derived evaluation comparison.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-derived-subsequence: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical exact derived subsequence comparisons.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-system-selected-derived-transition: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns The specified tensor-adjoint selected derived transition.

lem-sf-ambient-adjunction-compositor-normalization vs lem-cbc-cochain-derived-adjunction: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized derived adjunction for a specified cochain left derived pair.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sp-subterminal-derived-image-calculus: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns K-injective derived direct-image comparisons for subterminal slices.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-normalized-left-extension: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Normalized left extension from a resolving class.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pur-completed-coefficient-pushforward-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Completed-coefficient pushforward restriction and strict reduction towers.

lem-sf-ambient-adjunction-compositor-normalization vs lem-kun-derived-adjoint-square-comparison: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Canonical right-derived comparison respects an exact adjoint square.

lem-sf-ambient-adjunction-compositor-normalization vs lem-pd-section-derived-pushpull-normalization: The new claim identifies both ordinary and system geometric c/e with their resolution/localization models and full composite adjunction normalization; the existing claim concerns Section equivalence and canonical derived push-pull adjunctions.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-unbounded-compact-support-proper-composition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Unbounded ordinary etale compact supports composed with a proper direct image.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-ambient-proper-open-pasting: the parent combines all five tasks and additionally derives both Gamma pasting laws and refinement consequences.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-native-weil-open-proper-interchange: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Proper/open interchange for native bounded constructible Weil complexes.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-semilinear-proper-open-mate-pasting: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Intrinsic proper/open mates and pasting for varying coefficient systems.

lem-sf-ambient-clopen-restriction-uniqueness vs def-coef-semilinear-proper-open-mate: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical semilinear proper/open adjunction mate.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-composition-projection-mate: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized compact-support composition satisfies the projection mate identity.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-proper-open-projection-mate: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized proper/open interchange commutes with projection.

lem-sf-ambient-clopen-restriction-uniqueness vs def-sf-semilinear-proper-open-comparisons: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs def-sf-etale-support-compositor: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical unbounded etale compact-support compositor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-trf-compact-composition-proper-square-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Compact-support composition along a proper square: closed and open normalizations.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-trf-compact-composition-tower-formula: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Computing finite pro-etale compact-support composition on a compatible tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-trf-finite-structural-maps-commshift: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical finite-coefficient structural maps commute with shifts.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-trf-proper-composition-site-transport: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Site comparison preserves compact-support composition with a proper factor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-trf-proper-open-site-transport: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Site comparison preserves finite proper/open interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sfb-proper-open-tower-single-unit-formula: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Single derived-unit formula in a proper/open tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sfb-proper-open-tower-successive-unit-formula: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Successive derived-unit formula in a proper/open tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sfb-proper-open-tower-derived-unit: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Derived-unit resolution calculation in a proper/open tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sfb-exact-compactification-unit-refinement: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized exact compactification units respect canonical refinements.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sfb-exact-compactification-unit-composition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Composition of normalized exact compact-support units.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-connected-torsor-module-descent: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Module descent on a connected finite torsor with natural geometric stalk comparisons.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-associated-module-comparisons: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Pullback and coefficient comparisons.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-module-descent-equivalence: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Additive module descent equivalence on a connected finite torsor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-ordinary-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Ordinary natural normalized evaluation before deck equivariance.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Gluing equivariant module sections.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-finite-ring-torsor-module-descent: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Recovery of a torsor-trivialized finite-ring module sheaf.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-equivariant-module-recover-linear: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Linear recovery for equivariant section transformations.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-graph-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Graph evaluation is injective for equivariant locally constant functions.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-section-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Existence of normalized torsor section evaluation.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Deck equivariance forced by naturality and diagonal normalization.

lem-sf-ambient-clopen-restriction-uniqueness vs def-weil-pbc-torsor-associated-module: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Associated module functor of equivariant locally constant sections.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-normalized-graph-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Ordinary normalized evaluation on a graph gives constant-sheaf coordinates.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Surjectivity of diagonal evaluation of torsor sections.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-etale-open-proper-interchange: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open extension by zero and proper derived pushforward interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-finite-ring-torsor-module-comparisons: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Pullback and unit comparisons for the associated module functor.

lem-sf-ambient-clopen-restriction-uniqueness vs def-weil-pbc-torsor-section-representation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical representation on sections over a torsor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-invariant-sections: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Invariant coefficient sections.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-diagonal-evaluation-bijective: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Objectwise bijectivity of graph evaluation.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-associated-module-essential-image: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Recovery of representations from constant torsor pullbacks.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-section-evaluation-bijective: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Bijectivity of normalized torsor section evaluation.

lem-sf-ambient-clopen-restriction-uniqueness vs def-weil-pbc-finite-ring-torsor-associated-module: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Associated module sheaf functor with arbitrary commutative coefficients.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-equivariant-presheaf-sheaf: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Equivariant locally constant torsor functions form a sheaf.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-section-evaluation-local: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized evaluation on an etale object with a torsor section.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-associated-module-full: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Fullness of the associated module functor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-torsor-diagonal-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Diagonal evaluation.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-constant-module-locally-constant: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Natural locally constant model of the constant module sheaf.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-unbounded-proper-open-adjunction-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Adjunction normalization of unbounded proper/open interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-pur-system-clopen-tensor-compatibility: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Proper/open tensor-mate interchange on varying-coefficient systems.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-weil-pbc-proper-open-identification-unit: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Unit normalization of the proper/open restriction identification.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-graph-sheaf-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Graph comparison agrees with the canonical map into direct image.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-normalized-proper-open-pasting: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Horizontal pasting for fixed normalized proper/open comparisons.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proper-open-coefficient-mate: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Coefficient and site squares for cartesian proper/open interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-exc-proetale-finite-cd-proper-open-interchange: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Deriving proper/open support under all-sheaf finite cohomological dimension.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-unbounded-proper-open-interchange: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-graph-geometric-base-change: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns The specified forward graph comparison at a geometric base change.

lem-sf-ambient-clopen-restriction-uniqueness vs def-cbc-strict-tower-composition-maps: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical strict-tower composition comparison maps.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-proper-open-comparison-site-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalization of the proper/open comparison under the site comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-exc-proetale-cartesian-open-injective-acyclic: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Proper acyclicity of injectives extended from an arbitrary Cartesian open.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-open-extended-injective-proper-acyclic: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open extension of an injective sheaf is acyclic for the proper right-hand map.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-normalized-proper-open-geometric-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Refinement and base change for fixed normalized proper/open comparisons.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-pur-clopen-ringed-module-gluing: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Exact module gluing across a finite clopen cover for arbitrary ring sheaves.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-compact-support-open-source-composition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Compact-support composition with a source open.

lem-sf-ambient-clopen-restriction-uniqueness vs def-cbc-finite-constant-coefficient-transport: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized finite scalar and etale-origin transport to constant coefficient modules.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-finite-graph-isomorphism: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns The specified graph comparison for finite etale morphisms.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proetale-proper-boundary-cohomology: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Boundary cohomology of an open-extended pro-etale injective on a proper scheme.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-shriek-open-tower-counit: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open compact-support composition on the pullback tower.

lem-sf-ambient-clopen-restriction-uniqueness vs def-sp-varying-ring-clopen-arrow-factors: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Separate the cartesian lift and clopen section factors before taking mates.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-cartesian-lift-pullback-equivalence: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Cartesian clopen lifts and equivalence of varying-ring inverse image.

lem-sf-ambient-clopen-restriction-uniqueness vs def-sp-varying-ring-proper-open-arrows: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Intrinsic varying-ring clopen proper/open arrows.

lem-sf-ambient-clopen-restriction-uniqueness vs def-pur-system-tensor-mate-arrows: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Canonical tensor and proper/open arrows for varying coefficient systems.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-pur-finite-clopen-derived-decomposition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Finite clopen decomposition of pro-etale derived coefficient categories.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-complete-proetale-refinement-exchange-coherence: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Refinement Exchange Coherence.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-pur-compact-support-strict-scalar-refinement: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Scalar mate compatibility with strict compactification refinements.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-unbounded-compact-support-comparisons: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Unbounded ordinary etale compact-support comparisons.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-finite-site-tower-paste: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Finite-site comparison of the proper/open compatible-tower word.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-shriek-tensor-composition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Tensor projection maps respect compact-support composition.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-clopen-arrow-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Compose the separately evaluated clopen arrow factors.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-open-base-change-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized coefficient evaluation of cartesian open base change.

lem-sf-ambient-clopen-restriction-uniqueness vs def-asd-compact-support-graph-comparison: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns The specified sheaf and unbounded derived graph comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proper-open-comparison-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Structural normalization of explicit proper/open comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-graph-derived-isomorphism: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Invertibility of the specified graph map on unbounded complexes.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-exc-proetale-proper-open-sheaf-comparison: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Proper/open comparison for pro-etale module sheaves.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-exc-etale-origin-proper-open-interchange: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Site transport preserves the canonical Cartesian proper/open interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-refinement-coefficient-mate: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Coefficient and site squares for the explicit refinement theta.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-compactification-projection-composition: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Projection maps respect the explicit proper/open compactification tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-proper-open-refinement-adjoint-projection: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Adjoint of the unbounded proper-open refinement comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-etale-compact-support-normalization: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalization of compactified etale support and its exchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proper-open-tower-comparison: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open-adjunction normalization of proper/open interchange on strict coefficient towers.

lem-sf-ambient-clopen-restriction-uniqueness vs def-cbc-strict-tower-open-extension: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized exact open extension on strict constant-coefficient towers.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-strict-tower-proper-open-calculus: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized proper/open calculus on strict pro-etale towers.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-clopen-section-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Normalized coefficient evaluation of the clopen section factor.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-pur-etale-horizontal-support-tower: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Etale compact-support composition on a pullback compactification tower.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns The cartesian open comparison on varying-ring systems relabels lifts.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-amb-shriek-open-exchange-adjoint: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open compact-support exchange is the extension-composition mate.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-graph-sheaf-normalization-transpose: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Transpose of graph comparison.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-asd-compact-support-graph-coherence: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Base-change, proper-refinement and identity equations for the graph map.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proetale-open-injective-proper-acyclic: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Open-extended injectives are proper-direct-image acyclic on pro-etale sites.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-ordinary-clopen-evaluation: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Ordinary coefficient evaluation preserves the single-square clopen arrow.

lem-sf-ambient-clopen-restriction-uniqueness vs def-cbc-strict-constant-tower-operations: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Strict constant-coefficient towers and normalized inverse/direct-image operations.

lem-sf-ambient-clopen-restriction-uniqueness vs def-cbc-strict-tower-proper-open-arrows: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Unit-normalized proper and open arrows on strict towers.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-proper-open-coefficient-mate-transposed: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Transposed coefficient mate identity for proper/open interchange.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-proper-open-interchange-coherence: The new claim is the ordinary/system abelian Hom restriction bijection for a geometrically constructed finite-type clopen factor, including its product-of-sections model; the existing claim concerns Proper/open interchange and its base-change and composition equations.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-adic-finite-exchange-encoding: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Finite quotient realization preserves the actual smooth-exchange mate.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sbc-derived-localization-comparison-data: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical derived étale-localization comparisons.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-restrict-scalars-pullback-square-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical coefficient comparisons preserve inverse-image square transport.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-base-change-restrict-scalars-arrow: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Étale base-change arrows commute with restriction of coefficients.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-reflector-square-mate-factorization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Factorization of a reflected square mate through its ambient mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-restrict-scalars-derived-adjunction-identities: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical coefficient comparisons preserve the derived adjunction.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-restrict-scalars-derived-exchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical coefficient comparisons commute with derived exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sbc-base-change-restrict-scalars-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coefficient comparison isomorphisms for the base-change source and target.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-unbounded-compact-support-proper-composition: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unbounded ordinary etale compact supports composed with a proper direct image.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-ambient-proper-open-pasting: the parent combines all five tasks and additionally derives both Gamma pasting laws and refinement consequences.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-native-weil-open-proper-interchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Proper/open interchange for native bounded constructible Weil complexes.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-semilinear-proper-open-mate-pasting: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Intrinsic proper/open mates and pasting for varying coefficient systems.

lem-sf-ambient-exact-clopen-comparison-localization vs def-coef-semilinear-proper-open-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical semilinear proper/open adjunction mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-adjunct-conjugate-open-factor: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Transport a mate through conjugation and cancel an open factor.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-composition-projection-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized compact-support composition satisfies the projection mate identity.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-proper-open-projection-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized proper/open interchange commutes with projection.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-coef-cartesian-section-adjoint-mates: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Adjoint mates on cartesian derived sections.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sf-semilinear-proper-open-comparisons: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sf-etale-support-compositor: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical unbounded etale compact-support compositor.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-bounded-below-derived-mate-model: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Bounded-below derived mates are computed by underived mates and comparison units.

lem-sf-ambient-exact-clopen-comparison-localization vs def-trf-topos-derived-base-change-map: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Derived base-change map for a commutative square of ringed topoi.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-compact-composition-proper-square-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Compact-support composition along a proper square: closed and open normalizations.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-compact-composition-tower-formula: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Computing finite pro-etale compact-support composition on a compatible tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-finite-structural-maps-commshift: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical finite-coefficient structural maps commute with shifts.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-proper-composition-site-transport: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Site comparison preserves compact-support composition with a proper factor.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-trf-proper-open-site-transport: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Site comparison preserves finite proper/open interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pc-derived-base-change-map: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical derived base-change morphism.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-proper-open-tower-single-unit-formula: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Single derived-unit formula in a proper/open tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-proper-open-tower-successive-unit-formula: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Successive derived-unit formula in a proper/open tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-proper-open-tower-derived-unit: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Derived-unit resolution calculation in a proper/open tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-exact-compactification-unit-refinement: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized exact compactification units respect canonical refinements.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sfb-proetale-projection-exchange-maps: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical projection and exchange maps on internal pro-etale modules.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-identity-open-underived-square-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Underived adjunction and pullback-square normalization at an identity open locus.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-exact-compactification-unit-composition: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Composition of normalized exact compact-support units.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-integral-quotient-section-mate-realization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Integral quotient scalar and geometric mate realization in section modules.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-ringed-kunneth-factorizations: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Two factorizations of the ringed-topos external product comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sfb-etale-proetale-scalar-counit-transposes: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Common counit transpose of the two site/scalar direct-image composites.

lem-sf-ambient-exact-clopen-comparison-localization vs def-a1-lisse-section-evaluation: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical evaluation of ordinary common-stage sections at a geometric point.

lem-sf-ambient-exact-clopen-comparison-localization vs def-a1-proper-sections-germ-and-moving-point: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical proper compact rational germs and semilinear moving points.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-ordinary-ringed-exchange-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Identity and pasting for ordinary ambient ringed exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pe-constant-exchange-encoding: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Constant scalar restriction identifies the ambient ringed exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs def-weil-pbc-adjunction-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Mate of a transformation under two adjunctions.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-ringed-slice-pullback-mate-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Slice pullback comparison is induced by the ringed localization square.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-exchange-mate-cube: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Naturality of the adjunction mate across a cube.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-derived-exchange-module-termwise: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns K-injective representative of the module derived exchange mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-strict-tower-exchange-mate-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Strict tower exchange agrees with the canonical mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-discrete-exchange-site-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical etale/pro-etale exchange comparison for arbitrary discrete rings.

lem-sf-ambient-exact-clopen-comparison-localization vs def-weil-pbc-four-arrows: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Four finite-level arrows.

lem-sf-ambient-exact-clopen-comparison-localization vs prop-weil-pbc-derived-inverse-image-adjunction: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Derived adjunction of inverse and direct image on D^+.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-etale-open-proper-interchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open extension by zero and proper derived pushforward interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-module-abelian-underived-exchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coefficient forgetting respects underived exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-finite-level-rectangle: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Finite-level exchange rectangle.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-module-abelian-stalk-exchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Forgetting module coefficients in the stalk of derived exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-exchange-forget-coefficients: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The derived exchange morphism commutes with forgetting the coefficient ring.

lem-sf-ambient-exact-clopen-comparison-localization vs def-weil-pbc-derived-square-iso: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Square isomorphism on bounded below derived categories.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-derived-exchange-unbounded-transport: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Transport of the exchange equation to arbitrary K-injective representatives.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-frobenius-exchange-restriction: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Finite-level exchange is the restricted ambient exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical coefficient comparisons intertwine derived exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-etale-underived-exchange-restriction: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Underived exchange along an etale morphism is the restriction identification.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-derived-exchange-bounded-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The bounded below exchange comparison equation.

lem-sf-ambient-exact-clopen-comparison-localization vs def-weil-pbc-strict-tower-operations: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Specified derived operations and mate on strict pro-etale module towers.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-intrinsic-finite-exchange-rectangle: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Finite exchange rectangle for intrinsic coefficient reduction.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-unbounded-proper-open-adjunction-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Adjunction normalization of unbounded proper/open interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-system-clopen-tensor-compatibility: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Proper/open tensor-mate interchange on varying-coefficient systems.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-ringed-coefficient-projection-cocycle: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coefficient projection cocycle for ordinary derived ringed diagrams.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-weil-pbc-proper-open-identification-unit: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unit normalization of the proper/open restriction identification.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-graph-sheaf-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Graph comparison agrees with the canonical map into direct image.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pur-scalar-pullback-representative-data: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical scalar/pullback representative data.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-normalized-proper-open-pasting: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Horizontal pasting for fixed normalized proper/open comparisons.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proper-open-coefficient-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coefficient and site squares for cartesian proper/open interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-exc-proetale-finite-cd-proper-open-interchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Deriving proper/open support under all-sheaf finite cohomological dimension.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-unbounded-proper-open-interchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-strict-tower-pullback-square-pasting: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Pasting of normalized strict-tower inverse-image squares.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-kun-commutative-exchange-evaluation-compatibility: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Raw class evaluation commutes with geometric chart pullback.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-graph-geometric-base-change: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The specified forward graph comparison at a geometric base change.

lem-sf-ambient-exact-clopen-comparison-localization vs def-cbc-strict-tower-composition-maps: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical strict-tower composition comparison maps.

lem-sf-ambient-exact-clopen-comparison-localization vs def-kun-commutative-exchange-raw-pullback: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical transport of represented raw classes through a commutative square.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-proper-open-comparison-site-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalization of the proper/open comparison under the site comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-strict-tower-direct-image-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coherence of canonical strict-tower direct image and its square mates.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-pullback-unit-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Identity unit law for actual varying-ring inverse-image compositors.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-exc-proetale-cartesian-open-injective-acyclic: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Proper acyclicity of injectives extended from an arbitrary Cartesian open.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pur-ringed-coefficient-projection-data: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized coefficient projection interfaces.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-open-extended-injective-proper-acyclic: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open extension of an injective sheaf is acyclic for the proper right-hand map.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-normalized-proper-open-geometric-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Refinement and base change for fixed normalized proper/open comparisons.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-compact-support-open-source-composition: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Compact-support composition with a source open.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-etale-scalar-pullback-existence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Existence of normalized derived scalar/pullback comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs def-cbc-finite-constant-coefficient-transport: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized finite scalar and etale-origin transport to constant coefficient modules.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pur-etale-scalar-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical derived etale scalar-change mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-finite-graph-isomorphism: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The specified graph comparison for finite etale morphisms.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pur-etale-scalar-pullback-iso: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical derived scalar and pullback isomorphism.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proetale-proper-boundary-cohomology: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Boundary cohomology of an open-extended pro-etale injective on a proper scheme.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-shriek-open-tower-counit: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open compact-support composition on the pullback tower.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sp-varying-ring-clopen-arrow-factors: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Separate the cartesian lift and clopen section factors before taking mates.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-cartesian-lift-pullback-equivalence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Cartesian clopen lifts and equivalence of varying-ring inverse image.

lem-sf-ambient-exact-clopen-comparison-localization vs def-sp-varying-ring-proper-open-arrows: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Intrinsic varying-ring clopen proper/open arrows.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-kun-derived-exchange-cube: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Derived exchange commutes around a commutative cube.

lem-sf-ambient-exact-clopen-comparison-localization vs def-pur-system-tensor-mate-arrows: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Canonical tensor and proper/open arrows for varying coefficient systems.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-complete-proetale-refinement-exchange-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Refinement Exchange Coherence.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-compact-support-strict-scalar-refinement: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Scalar mate compatibility with strict compactification refinements.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-unbounded-compact-support-comparisons: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unbounded ordinary etale compact-support comparisons.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-scalar-tensor-pullback-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Scalar/tensor pullback normalization on a K-flat representative.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proetale-projection-mate-identification: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Identify the prescribed pro-etale scalar/direct-image mate with the ringed-topos mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-finite-site-tower-paste: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Finite-site comparison of the proper/open compatible-tower word.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-shriek-tensor-composition: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Tensor projection maps respect compact-support composition.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-clopen-arrow-evaluation: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Compose the separately evaluated clopen arrow factors.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-open-base-change-evaluation: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized coefficient evaluation of cartesian open base change.

lem-sf-ambient-exact-clopen-comparison-localization vs def-asd-compact-support-graph-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The specified sheaf and unbounded derived graph comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs def-kun-commutative-derived-exchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Derived exchange for an arbitrary commutative square of schemes.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proper-open-comparison-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Structural normalization of explicit proper/open comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-kun-commutative-exchange-class-compatibility: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The exchange mate transports higher-image raw classes.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-graph-derived-isomorphism: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Invertibility of the specified graph map on unbounded complexes.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-exc-proetale-proper-open-sheaf-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Proper/open comparison for pro-etale module sheaves.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-exc-etale-origin-proper-open-interchange: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Site transport preserves the canonical Cartesian proper/open interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-etale-scalar-pullback-uniqueness: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Uniqueness of normalized derived scalar/pullback comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-refinement-coefficient-mate: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Coefficient and site squares for the explicit refinement theta.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-compactification-projection-composition: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Projection maps respect the explicit proper/open compactification tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-proper-open-refinement-adjoint-projection: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Adjoint of the unbounded proper-open refinement comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-etale-compact-support-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalization of compactified etale support and its exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proper-open-tower-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open-adjunction normalization of proper/open interchange on strict coefficient towers.

lem-sf-ambient-exact-clopen-comparison-localization vs def-cbc-strict-tower-open-extension: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized exact open extension on strict constant-coefficient towers.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-strict-tower-proper-open-calculus: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized proper/open calculus on strict pro-etale towers.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-clopen-section-evaluation: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalized coefficient evaluation of the clopen section factor.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pur-etale-horizontal-support-tower: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Etale compact-support composition on a pullback compactification tower.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns The cartesian open comparison on varying-ring systems relabels lifts.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-amb-shriek-open-exchange-adjoint: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open compact-support exchange is the extension-composition mate.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-graph-sheaf-normalization-transpose: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Transpose of graph comparison.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-asd-compact-support-graph-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Base-change, proper-refinement and identity equations for the graph map.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-exc-support-scalar-projection-normalization: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Normalization of support scalar mate as a projection arrow.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proetale-open-injective-proper-acyclic: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Open-extended injectives are proper-direct-image acyclic on pro-etale sites.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-kun-unbounded-abelian-exchange-comparison: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unbounded coefficient forgetting identifies canonical etale exchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-ordinary-clopen-evaluation: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Ordinary coefficient evaluation preserves the single-square clopen arrow.

lem-sf-ambient-exact-clopen-comparison-localization vs def-cbc-strict-constant-tower-operations: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Strict constant-coefficient towers and normalized inverse/direct-image operations.

lem-sf-ambient-exact-clopen-comparison-localization vs def-cbc-strict-tower-proper-open-arrows: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Unit-normalized proper and open arrows on strict towers.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-proper-open-coefficient-mate-transposed: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Transposed coefficient mate identity for proper/open interchange.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-proper-open-interchange-coherence: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Proper/open interchange and its base-change and composition equations.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-pod-frobenius-exchange-degree-zero: The new claim is the exact-chain-localization certificate identifying the single intrinsic alpha and its mate in both ambient categories, not a pasting or projection identity; the existing claim concerns Degree-zero Frobenius exchange is the underived section-pullback mate.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-ambient-proper-open-pasting: the parent combines all five tasks and additionally derives both Gamma pasting laws and refinement consequences.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-semilinear-proper-open-mate-pasting: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Intrinsic proper/open mates and pasting for varying coefficient systems.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-composition-projection-mate: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Normalized compact-support composition satisfies the projection mate identity.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-proper-open-projection-mate: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Normalized proper/open interchange commutes with projection.

lem-sf-ambient-underived-clopen-pasting vs def-sf-semilinear-proper-open-comparisons: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-normalized-proper-open-pasting: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Horizontal pasting for fixed normalized proper/open comparisons.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-complete-proetale-composition-pasting-coherence: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Composition Pasting Coherence.

lem-sf-ambient-underived-clopen-pasting vs lem-sp-ordinary-vertical-pasting-transport: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Transport of a vertical square-pasting equation through coherent comparisons.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-unbounded-proper-open-interchange: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Unbounded torsion-coefficient proper/open interchange with its canonical maps.

lem-sf-ambient-underived-clopen-pasting vs def-cbc-strict-tower-composition-maps: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Canonical strict-tower composition comparison maps.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-normalized-proper-open-geometric-normalization: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Refinement and base change for fixed normalized proper/open comparisons.

lem-sf-ambient-underived-clopen-pasting vs def-cbc-finite-constant-coefficient-transport: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Normalized finite scalar and etale-origin transport to constant coefficient modules.

lem-sf-ambient-underived-clopen-pasting vs lem-sp-varying-ring-proper-open-pasting: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Clopen proper/open projections and pasting over a varying ring system.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-complete-proetale-refinement-exchange-coherence: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Refinement Exchange Coherence.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-unbounded-proper-open-pasting: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Pasting and identity normalizations of unbounded proper/open interchange.

lem-sf-ambient-underived-clopen-pasting vs lem-pur-compact-support-site-coherence: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Compact-support site comparison respects compactification calculus.

lem-sf-ambient-underived-clopen-pasting vs lem-pur-compact-support-strict-scalar-refinement: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Scalar mate compatibility with strict compactification refinements.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-unbounded-proper-open-horizontal-composition: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Horizontal composition of unbounded proper/open interchange.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-compact-support-staircase-expansion: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Expansion of binary compact-support tower comparisons on a fixed staircase.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-unbounded-proper-open-composition: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Vertical and horizontal composition of unbounded proper/open interchange.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-tower-composition-refinement: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Compatible-tower composition commutes with proper refinements.

lem-sf-ambient-underived-clopen-pasting vs def-cbc-strict-tower-open-extension: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Normalized exact open extension on strict constant-coefficient towers.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-strict-tower-proper-open-calculus: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Normalized proper/open calculus on strict pro-etale towers.

lem-sf-ambient-underived-clopen-pasting vs def-cbc-strict-constant-tower-operations: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Strict constant-coefficient towers and normalized inverse/direct-image operations.

lem-sf-ambient-underived-clopen-pasting vs def-cbc-strict-tower-proper-open-arrows: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Unit-normalized proper and open arrows on strict towers.

lem-sf-ambient-underived-clopen-pasting vs lem-amb-derived-compact-support-composition-coherence: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Structural coherence of three derived images and open extensions.

lem-sf-ambient-underived-clopen-pasting vs def-sp-proper-open-calculus: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Coherent proper/open interchange data on a category of schemes.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-proper-open-interchange-coherence: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Proper/open interchange and its base-change and composition equations.

lem-sf-ambient-underived-clopen-pasting vs lem-sp-ordinary-horizontal-pasting-transport: The new claim consists of underived ordinary/system alpha pasting with restrictions of the individual factors explicitly fixed, and identity-square normalization; the existing claim concerns Transport of a horizontal square-pasting equation through coherent comparisons.

lem-sf-ambient-pullback-tensor-coherence vs lem-sf-semilinear-compositor-coherence: states associative d/c/e for varying systems, but not the ordinary single-coefficient geometric realization, K-flat tensor equation or simultaneous resolution/localization certificates required here.

lem-sf-ambient-pullback-tensor-coherence vs lem-sf-semilinear-proper-open-mate-pasting: states derived system mates, including scalar/evaluation comparisons; it does not provide the underived ordinary-and-system restriction bijection or the local chain-map certificates in these new tasks.

lem-sf-ambient-pullback-tensor-coherence vs lem-sp-varying-ring-proper-open-pasting: states varying-ring derived system alpha/Gamma pasting, whereas these tasks additionally concern the ordinary single-coefficient realization and explicit underived restriction/chain-localization certificates; none merely restates its system conclusion.

lem-sf-ambient-pullback-tensor-coherence vs lem-cbc-normalized-proper-open-pasting: assumes fixed underived and derived comparison isomorphisms on bounded-below etale modules and gives horizontal pasting, not this intrinsic clopen pro-etale construction.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sf-semilinear-compositor-coherence: states associative d/c/e for varying systems, but not the ordinary single-coefficient geometric realization, K-flat tensor equation or simultaneous resolution/localization certificates required here.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sf-semilinear-proper-open-mate-pasting: states derived system mates, including scalar/evaluation comparisons; it does not provide the underived ordinary-and-system restriction bijection or the local chain-map certificates in these new tasks.

lem-sf-ambient-adjunction-compositor-normalization vs lem-sp-varying-ring-proper-open-pasting: states varying-ring derived system alpha/Gamma pasting, whereas these tasks additionally concern the ordinary single-coefficient realization and explicit underived restriction/chain-localization certificates; none merely restates its system conclusion.

lem-sf-ambient-adjunction-compositor-normalization vs lem-cbc-normalized-proper-open-pasting: assumes fixed underived and derived comparison isomorphisms on bounded-below etale modules and gives horizontal pasting, not this intrinsic clopen pro-etale construction.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-semilinear-compositor-coherence: states associative d/c/e for varying systems, but not the ordinary single-coefficient geometric realization, K-flat tensor equation or simultaneous resolution/localization certificates required here.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sf-semilinear-proper-open-mate-pasting: states derived system mates, including scalar/evaluation comparisons; it does not provide the underived ordinary-and-system restriction bijection or the local chain-map certificates in these new tasks.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-sp-varying-ring-proper-open-pasting: states varying-ring derived system alpha/Gamma pasting, whereas these tasks additionally concern the ordinary single-coefficient realization and explicit underived restriction/chain-localization certificates; none merely restates its system conclusion.

lem-sf-ambient-clopen-restriction-uniqueness vs lem-cbc-normalized-proper-open-pasting: assumes fixed underived and derived comparison isomorphisms on bounded-below etale modules and gives horizontal pasting, not this intrinsic clopen pro-etale construction.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-semilinear-compositor-coherence: states associative d/c/e for varying systems, but not the ordinary single-coefficient geometric realization, K-flat tensor equation or simultaneous resolution/localization certificates required here.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sf-semilinear-proper-open-mate-pasting: states derived system mates, including scalar/evaluation comparisons; it does not provide the underived ordinary-and-system restriction bijection or the local chain-map certificates in these new tasks.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-sp-varying-ring-proper-open-pasting: states varying-ring derived system alpha/Gamma pasting, whereas these tasks additionally concern the ordinary single-coefficient realization and explicit underived restriction/chain-localization certificates; none merely restates its system conclusion.

lem-sf-ambient-exact-clopen-comparison-localization vs lem-cbc-normalized-proper-open-pasting: assumes fixed underived and derived comparison isomorphisms on bounded-below etale modules and gives horizontal pasting, not this intrinsic clopen pro-etale construction.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-semilinear-compositor-coherence: states associative d/c/e for varying systems, but not the ordinary single-coefficient geometric realization, K-flat tensor equation or simultaneous resolution/localization certificates required here.

lem-sf-ambient-underived-clopen-pasting vs lem-sf-semilinear-proper-open-mate-pasting: states derived system mates, including scalar/evaluation comparisons; it does not provide the underived ordinary-and-system restriction bijection or the local chain-map certificates in these new tasks.

lem-sf-ambient-underived-clopen-pasting vs lem-sp-varying-ring-proper-open-pasting: states varying-ring derived system alpha/Gamma pasting, whereas these tasks additionally concern the ordinary single-coefficient realization and explicit underived restriction/chain-localization certificates; none merely restates its system conclusion.

lem-sf-ambient-underived-clopen-pasting vs lem-cbc-normalized-proper-open-pasting: assumes fixed underived and derived comparison isomorphisms on bounded-below etale modules and gives horizontal pasting, not this intrinsic clopen pro-etale construction.

## Review by Q144

I read the parent and all ten original steps, the Six Functors chapter and sk-rem-sf-pf-done unit, the current main-20261015 fix-prop-projection-formula proof, and Stacks more-etale.tex lemmas 0F7B/0F7C/0F7D and sites-cohomology.tex remarks 07A7/0E46/0E47. The Stacks results are etale statements; I have explicitly labeled the pro-etale/system extensions as agent arguments. I read sites-modules.tex 03D3, sites-cohomology.tex 0D6E and sites.tex 04TS for the new tasks. No disallowed source route is used.

Return repair: this is a substantive five-way extraction, not a shorter paraphrase. Each new task is supplied statement-only with actual searches. The complete original proof below makes it possible to recover every former argument. The workloads are local-tensor/K-flat coherence, adjoint/compositor normalization, geometric clopen gluing, exact-localization identification, and two underived restriction calculations. None contains the entire theorem, and the parent must still localize and take mates.

Parent Step 1 uses the new pullback/tensor task for d and the tensor equation, then the new adjunction/compositor task for c/e, including the resolution normalization and the threefold Hom bijection. I checked that these are conclusions of those statements, rather than claims available only in their future proofs. Their hypotheses match the two ambient categories, with no normalized-system assumption.

Parent Step 2 uses the new clopen task for both geometry and its abelian restriction bijection, and the exact-localization task for the identification of beta, alpha and the displayed proper mate. I checked that the projector is towards the selected component, not its inverse, and that both ordinary and simultaneous-system maps are expressly included.

Parent Step 3 uses the underived pasting task for both A and B. I opened lem-weil-pbc-exact-functor-derived-factorization: its conclusion says termwise exact functors descend without resolutions. I opened lem-weil-pbc-localization-universal-property: clause 2 lifts transformations and respects identity/composition, and clause 3 detects equality after localization. This supplies the descent of the underived equations, not an appeal to evaluated derived equality.

Parent Step 4 uses lem-weil-pbc-mate-pasting clauses 2 and 1. I checked all four left adjoints in clause 2 and all functor slots in clause 1 against the explicit substitutions in the parent step. The displayed Gamma orientations agree. The compositors used here are the adjunction-compatible ones already furnished by Step 1, so no arbitrary comparison has been substituted.

Parent Step 5 uses the identity clause 4 of that same mate node and the definition of compactification refinements. I read def-weil-compactifications-refinements: the refinement is proper and satisfies u j_1=j_2. Substitution r=1 gives exactly an allowed proper/open square. The remaining tower application is the same substitution on each intermediate square; it introduces no new theorem.

Hypotheses and small cases: for the clopen task I checked b is base-changed open, q is separated because p is proper, and qs=r is proper; proper-over-separated therefore makes s proper, and proper immersion makes it closed. Finite type follows by base change and composition, so the existing finite-clopen decomposition can apply without a separated structure map. For U empty the selected summand is zero and every indicated map into it is unique. For C empty projection is identity; for the Cartesian square s is identity; both identity orientations give the canonical unit maps. Disconnected and nonseparated-over-k schemes cause no change because separatedness is relative to p only. For systems the product-of-sections inverse commutes with arbitrary coefficient homomorphisms, including the nonflat quotient transitions A_(n+1) to A_n. K-flat comparison is on the diagram site, not inferred by faithfulness of evaluation. Zero complexes and unbounded complexes are included. No Gamma invertibility is inferred.

B--E self-check: all new nodes have self-contained TeX statements, notion references, source tags with labels, blueprint.from.place and via, actual semantic/Loogle/grep records, no proofs and no proof dependencies. I searched existing candidates before creating them, including the stronger system-only neighbors. The parent retains its exact statement. Every parent use has a verbatim statement quote in citations.json; no step depends on the proof of a cited node. The new nodes do not depend on the parent. No non-elementary parent step exceeds 2000 characters. Generic category-theory tools are declared in split_report.tool_uses; no chapter/unit route is changed.

Mathlib source checks: read SheafOfModules.pullbackComp (PullbackContinuous.lean:167), conjugateEquiv_pullbackComp_inv (:177), pullback_assoc (:193) and its unit lemmas. These give the ordinary categorical component, not the derived tensor/system assertion. Read Adjunction.leftAdjointCompIso (CompositionIso.lean:73) and its conjugate formula, and Adjunction.localization (Localization/Adjunction.lean:89), localization_unit_app (:118) and counit formula. These are generic tools already represented by existing DAG nodes and do not close a whole new geometric task. Other semantic hits concern scheme structure sheaves, topological gluing or profinite limits rather than these ambient comparisons. The failed initial Loogle pattern names an unknown identifier; a corrected localization query was then run successfully.

## Original argument inventory (verbatim, retained for future workers)

The following is report material only: it is not a proof assigned to any new unsplit node. Assignment of each old step is specified above.

### Old Step 1

First fix the comparisons on module sheaves, before deriving. The direct-image section identifications for a composite are induced by the unique fibre-product isomorphism; the two identifications for three maps coincide because their projections coincide. Taking the uniquely adjunction-compatible inverse-image comparison gives the unital, associative pullback compositor. The module comparison is the explicit one in lem-sf-proetale-tensor-composition-unit: on local tensors it sends $(m\otimes a)\otimes b$ to $m\otimes c_u(a)b$. Its unit equation identifies it with the adjunction comparison, not merely an isomorphism of functors. Constant coefficient identifications are compatible with composition by lem-pur-proetale-constant-ring-composition. In (b) the same formulas commute with every semilinear transition: restriction and multiplication commute with the ring homomorphisms $A_{n+1}\to A_n$. Thus they are actual maps of systems. Apply the exact-functor localization to these maps on complexes to obtain $d$. The simultaneous models of lem-coef-semilinear-derived-sections identify this construction with the specified system pullbacks.

Original cited statements: lem-weil-pbc-site-morphism-composition, lem-sf-proetale-tensor-composition-unit, lem-pur-proetale-constant-ring-composition, lem-weil-pbc-exact-functor-derived-factorization, lem-coef-semilinear-derived-sections.

Original source: literature/stacks-project/sites.tex; Tag 03CB (lemma-composition-morphisms-sites); module lift: sites-modules.tex Tag 03D3 (lemma-adjoint-push-pull-modules); explicit system extension written here.

### Old Step 2

For $P_u\dashv S_u$, use the composite unit and counit of def-weil-pbc-composite-adjunction. The inverse conjugate of $d$ gives $c:S_vS_u\cong S_{vu}$, carrying these composite units and counits to the canonical ones. For ordinary unbounded derived direct images this is the canonical resolution comparison by lem-sfb-derived-composition-adjunction-normalization; in (b) apply the same exact-left-adjoint argument on the stipulated ringed diagram category, with its adjunctions supplied by lem-coef-semilinear-derived-sections. For open maps the comparison between $J_bJ_j$ and $J_{bj}$ is uniquely determined by the right-adjoint comparison $P_jP_b\cong P_{bj}$ and its unit equation, by lem-weil-pbc-conjugate-iso-unit-equation. This gives $e$ with precisely the asserted normalization. Both parenthesizations for three maps have the same adjunction transpose, since $d$ is associative and the composite Hom bijection is the same three successive bijections. Injectivity of transposition identifies them; the identity case is identical with one identity Hom bijection. This proves naturality, associativity, unitality and compatibility with the composite adjunction for $c,e$.

Original cited statements: def-weil-pbc-composite-adjunction, lem-weil-pbc-conjugate-iso-unit-equation, lem-sfb-derived-composition-adjunction-normalization, lem-coef-semilinear-derived-sections.

Original source: literature/stacks-project/sites-cohomology.tex; Tag 0D6E (lemma-derived-pushforward-composition), using derived.tex Tag 09T5 (lemma-derived-adjoint-functors); uniqueness of adjunction comparisons.

### Old Step 3

The tensor comparison also respects $d$. The monoidal inverse-image comparisons of lem-weil-pbc-left-exact-site-inverse-image-tensor give this first over $\mathbf Z$. Passing to relative tensor products gives the same equality: after the coefficient identifications a local tensor $x\otimes y$ is sent by either route to $P_ux\otimes P_uy$, with any intermediate scalar multiplied into the final scalar. This follows directly from the formula for the module compositor in Step 1 and the balancing relation, so the equality holds on the sheaf tensor products. To derive it take K-flat resolutions with flat terms as in lem-weil-pbc-ringed-topoi-derived-tensor-pullback. Their successive pullbacks remain K-flat with flat terms, and both comparisons are the maps just checked on their total tensor complexes; localization gives $\mu_{vu}=\mu_u\circ P_u(\mu_v)$ after $d$ and tensor associators. In (b) use K-flat complexes on the ringed diagram site and the simultaneous tensor construction of lem-coef-semilinear-derived-sections. The scalar formula is already an equality of system chain maps, so localization gives the asserted system equality.

Original cited statements: lem-weil-pbc-left-exact-site-inverse-image-tensor, lem-sf-proetale-tensor-composition-unit, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-coef-semilinear-derived-sections.

Original source: literature/stacks-project/sites-modules.tex; Tag 03D3 (lemma-adjoint-push-pull-modules); relative tensor balancing and K-flat derivation of the inverse-image tensor comparison.

### Old Step 4

For a square $Q$, the projection $b:V_W\to V$ is an open immersion by base change of $i$. Under this identification $V_W$ is the open inverse image $p^{-1}(W)$; since $k_1$ is open and factors through $b$, its factor $s$ is open as well. The map $q$ is separated, being a base change of the separated map $p$. Since $qs=r$ is proper, lem-weil-pbc-proper-over-separated makes $s$ proper. The proper-immersion lemma then makes $s$ closed. Thus $V_W=s(U)\amalg C$ for the complementary open $C$. Notice that only separatedness of $p$ over $Z$ was used, and no separated structure morphism to $k$ was required. Moreover $q$ is of finite type by finite-type base change from $p$, and $V_W\to W\to\operatorname{Spec}k$ is of finite type by composition, using lem-sfb-finite-type-composition-base-change. This verifies the finite-type hypothesis of the clopen-decomposition node used next.

Original cited statements: lem-weil-pbc-open-immersion-base-change, lem-weil-pbc-separated-base-change, lem-weil-pbc-proper-over-separated, lem-weil-pbc-proper-immersion-closed, lem-sfb-finite-type-composition-base-change.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B-0F7D: open-immersion case; clopenness is the proper-over-separated and proper-immersion factorization underlying the normalization.

### Old Step 5

We shall check the pasting of $a$ on module sheaves. For the disjoint open cover $V_W=s(U)\amalg C$, the module equivalence in lem-pur-finite-clopen-derived-decomposition identifies $F$ with $(s^*F,F|_C)$ and $s_!G$ with $(G,0)$. Consequently a map $F\to s_!G$ is uniquely determined by its restriction $s^*F\to G$, and the projection $F\to s_!s^*F$ is $(1,0)$. For semilinear systems apply this sheaf equivalence at every $n$. Its explicit product-of-sections inverse commutes with restriction of scalars, so the equivalence and projection commute with all transition maps. A morphism of systems is a compatible family of component maps; hence the same uniqueness follows in the abelian system category. Combining this with full faithfulness of $b_!$, supplied by the open unit normalization, shows that a module or system map $b_!F\to k_{1!}G=b_!s_!G$ is uniquely determined by its restriction to $U$. This is a sheaf/system calculation; it makes no assertion that derived evaluation is faithful.

Original cited statements: lem-pur-finite-clopen-derived-decomposition, lem-sf-open-tensor-normalization.

Original source: literature/stacks-project/sites.tex; Tag 04TS (lemma-mapping-property-glue), specialized to the two disjoint open pieces; elementary extension from the cited module equivalence to semilinear systems.

### Old Step 6

Construct the sheaf comparison $a_Q$ by the open base-change isomorphism followed by $(1,0)$ in Step 5 and the open/pullback compositors. Its restriction to $U$ is the identity $r^*M\to r^*M$: the restricted base-change map is the identity under the open units, and so is the projection on the selected component. It is the unique map with this property, since its source is $b_!q^*M$ after open base change and Step 5 applies. All operations in this construction are exact functors, so it gives a chain map on every complex and descends to the unbounded derived categories. The localized open adjunction has the localized unit and counit by lem-sfb-adjunction-localization; therefore the localized open base-change map is exactly the unit-normalized derived $\beta$ of lem-sf-open-tensor-normalization, not an alternative isomorphism. It follows that the localized $a_Q$ is the intrinsic derived clopen composite in the question. Taking its mate by def-weil-pbc-adjunction-mate gives the displayed formula for $\Gamma_Q$. The formula is the same $\alpha,\gamma$ normalization explicitly specified by lem-sf-proper-open-projection-mate, in both coefficient settings.

Original cited statements: lem-sf-open-tensor-normalization, lem-weil-pbc-exact-functor-derived-factorization, lem-sfb-adjunction-localization, def-weil-pbc-adjunction-mate, lem-sf-proper-open-projection-mate.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7B (lemma-shriek-proper-and-open), map normalization; sites-cohomology.tex Tag 07A7 (remark-base-change), proper-adjunction transpose; agent clopen construction in the stated ambient categories.

### Old Step 7

For vertical pasting, label the rows $U_a\xrightarrow{j_a}V_a$ for $a=0,1,2$, with proper maps $r_a:U_{a-1}\to U_a$, $p_a:V_{a-1}\to V_a$ for $a=1,2$. On module sheaves form
$$A=(a_{Q_1}P_{r_2})\circ(P_{p_1}a_{Q_2}):P_{p_1}P_{p_2}J_{j_2}\longrightarrow J_{j_0}P_{r_1}P_{r_2},$$
where here $P,J$ denote underived exact functors. After restricting along $j_0$, the second factor is the pullback by $r_1$ of $P_{j_1}a_{Q_2}=1$, since $p_1j_0=j_1r_1$; the first factor restricts to $1$ by Step 6. Thus $P_{j_0}A=1$. Identify its source by open base change with $b_{\rm out,!}q_{\rm out}^*$ and its target with $b_{\rm out,!}s_{\rm out,!}(r_2r_1)^*$. The clopen uniqueness of Step 5 for the outer square identifies $A$ with its intrinsic $a$. This proves the geometric vertical identity before localization, also for system sheaves.

Original cited statements: lem-sf-open-tensor-normalization.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7C (lemma-shriek-proper-and-open-compose); explicit clopen-normalization verification for the open case.

### Old Step 8

For horizontal pasting, label the two squares by top opens $k_1:U\to V$, $k_2:V\to T$, bottom opens $i_1:W\to Z$, $i_2:Z\to Y$, and proper maps $r,p,q$. On module sheaves the pasted map is
$$B=(J_{k_2}a_{Q_1})\circ(a_{Q_2}J_{i_1}):P_qJ_{i_2}J_{i_1}\longrightarrow J_{k_2}J_{k_1}P_r.$$
Restrict along $k_2k_1$: the factor $a_{Q_2}J_{i_1}$ becomes the identity on $P_pJ_{i_1}$ after restriction to $V$, and the remaining factor becomes $P_{k_1}a_{Q_1}=1$. Hence the restriction of $B$ is identity. As in Step 7 its source is extension from the outer base-changed bottom open and its target is extension from the selected clopen component. Step 5 identifies it with the intrinsic $a$ of the outer square. The identifications here are precisely $e,d$ fixed in Steps 1-2. This proves the horizontal identity as module and system maps.

Original cited statements: lem-sf-open-tensor-normalization.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7D (lemma-shriek-proper-and-open-compose-horizontal); explicit clopen-normalization verification for the open case.

### Old Step 9

Apply the exact functors termwise to complexes in Steps 7-8. The localization universal property carries these equalities of natural transformations, their compositions and their compositors to equalities on the whole unbounded derived categories. Step 6 identifies the resulting maps with the intrinsic $a_Q$ there. Apply clause 2 of lem-weil-pbc-mate-pasting to Step 7, with $L_1=P_{r_2}$, $L_3=P_{r_1}$, $L_2=P_{p_2}$, $L_4=P_{p_1}$, $G=J_{j_2}$, $H=J_{j_1}$, $K=J_{j_0}$. It gives
$$\Gamma_{Q_2Q_1}=(S_{p_2}\Gamma_{Q_1})\circ(\Gamma_{Q_2}S_{r_1}).$$
Apply clause 1 of the same node to Step 8, with $L_1=P_r,L_2=P_p,L_3=P_q,G=J_{i_1},G_2=J_{i_2},H=J_{k_1},H_2=J_{k_2}$. It gives
$$\Gamma_{Q_2Q_1}=(\Gamma_{Q_2}J_{k_1})\circ(J_{i_2}\Gamma_{Q_1}).$$
The composite adjunctions are those of def-weil-pbc-composite-adjunction, so inserting $c,d,e$ is justified by Step 2. In (b) these are localizations and adjunction transposes in the system category itself, with the simultaneous models of lem-coef-semilinear-derived-sections. No equality is inferred from equalities of evaluated derived maps.

Original cited statements: lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-localization-universal-property, lem-weil-pbc-mate-pasting, def-weil-pbc-composite-adjunction, lem-coef-semilinear-derived-sections.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7C-0F7D, formal mate forms; sites-cohomology.tex Tags 0E46-0E47 (remark-compose-base-change, remark-compose-base-change-horizontal).

### Old Step 10

With identity vertical maps the square has equal horizontal opens, its clopen factor is the identity, and $a_Q$ is the identity on open extension under the units; its proper-adjunction mate is the same identity. With identity horizontal maps the proper maps coincide, $a_Q=1_{P_p}$, and clause 4 of lem-weil-pbc-mate-pasting gives $\Gamma_Q=1_{S_p}$. For a refinement $u$ the definition gives $uj_1=j_2$, with proper edges $1,u$ and open edges $j_1,j_2$, so it is among the squares already treated. Every intermediate proper/open square in a compatible refinement tower has precisely the hypotheses used in Steps 4-9, hence the same identities apply. The construction used no constructibility, Tor, boundedness, etale-origin, completed coefficient or cartesian-system condition. It constructs natural transformations on the stated categories, without asserting their invertibility.

Original cited statements: lem-weil-pbc-mate-pasting, def-weil-compactifications-refinements.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7C-0F7D, identity cases and applications to compactification refinements.
