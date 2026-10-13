# Upstream review of our bulk PRs, 2026-10-13

fuxi-bot (the upstream review bot) requested changes on #1424 and #1428 (formal-arithmetic-geometry/weil-conjectures, base slopmaster2).
Each point below is queued as a repair item (coord/repairs.txt) on the module named. Upstream paths are
WeilConjectures/<X>.lean for our Sheaf/<X>.lean. Fix the point in our library; false statements are corrected first,
then proved (roles/worker.md rule 7). Duplicates: delete ours and re-point every caller to the existing declaration.

## Points and modules

- #1424 [false statement] Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps: tower_limit_exact_of_coordinate_maps is false (alpha/beta need not commute with transitions; counterexample F_n=R zero maps, G_n=R identity, H=0, alpha=id, beta=0, U=V=0). Add naturality hypotheses as in TowerLimitInducedMaps (or take natural transformations), then prove.
- #1424 [replace] Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps: tower_limit_induced_maps is limMap (NatTrans.ofOpSequence ...): prove it or replace by that construction.
- #1424 [hollow data] Sheaf.AlgebraicGeometry.ConstantGroupScheme: constantGroupSchemeMultiplication is Classical.choose of a sorry (sorry-bodied data). Construct m directly (Cover.glueMorphisms on openCoverOfLeftRight, or Sigma.desc after identifying the fibre square with the coproduct over E x E), then prove the two properties.
- #1424 [use Mathlib] Sheaf.CategoryTheory.SiteCoveringsCommonRefinement: derive siteCoverings_common_refinement and the finite version from Mathlib ZeroHypercover.inter / PreZeroHypercover.interFst/interSnd (Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean); transport along IsPullback.isoPullback; iterate inter for the finite version.
- #1424 [duplicate] Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso: Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion duplicates Hom.isIso_residueFieldMap (upstream ConstructibleSheaf/UniversalHomeomorphism.lean): remove it and re-point callers.
- #1424 [duplicate] Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison: Abelian.Ext.exactFunctorCompositionComparison duplicates Abelian.Ext.mapExactFunctor_comp_mk0_eq (upstream Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean) minus EnoughInjectives: generalise the existing lemma instead, re-point callers.
- #1424 [duplicate] Sheaf.CategoryTheory.ExtExactFunctorIdentityComparison: exactFunctorIdentityComparison is the G2 = identity case: derive it from mapExactFunctor_eq_of_iso + mapExactFunctor_id.
- #1424 [duplicate] Sheaf.CategoryTheory.MapExtendHomology: mapExtendTermIso / mapExtendComplexIso duplicate HomologicalComplex.mapExtendX / mapExtendIso (upstream FromJoel/Algebra/Homology/Embedding/ExtendMap.lean): use those.
- #1424 [duplicate] Sheaf.Algebra.Homology.TensorBicomplex: tensorBicomplex / tensorBicomplexMap are Mathlib's ((Functor.mapBifunctorHomologicalComplex (curriedTensor _) _ _).obj P).obj Q and its map: use those.
- #1424 [duplicate] Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch: liftedCommGrpBranch only packages Functor.mapCommGrp / Adjunction.mapCommGrp in an exists: use those directly.
- #1424 [over-hypothesised] Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerCone: derivedCategory_towerLimit_cone: HasDerivedCategory, CountableAB4Star, hP, EnoughInjectives, IsKInjective are unused; the conclusion only says a N^op-diagram of complexes has a limit. Drop the unused hypotheses so the statement says what it proves.
- #1428 [false statement] Sheaf.Topology.SetsExtensionByEmptyAdjunction: extensionByEmpty_adjunction_stalks: the conjunct extensionByEmptyPresheaf U ⊣ (pullback ⋙ presheafToSheaf) is false (U = ⊤ gives inclusion left adjoint to sheafification; counterexample on discrete {a,b}). Drop the conjunct or use plain presheaf restriction as right adjoint.
- #1428 [false statement] Sheaf.AlgebraicGeometry.Modules.DeterminantSplitComparisonLocal: determinant_split_comparison_restriction: c is unconstrained so hd does not force d to commute with restriction (counterexample X = Spec Z, r1=0, r2=r3=1, X2=X3=O, g=id, rescale d W and c W by -1 off V). Require g ∘ c = id, or prove naturality together with existence in the _local lemma.
- #1428 [false statement] Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlatCore: stalk_normalization_depth_two_section_flat_core is false (the file's own counterexample A = Q[x^2,xy,y^2], U punctured cone). Add the rational-point / dense-fibre hypothesis of Stacks 0EYJ (cf. hclosed in SmoothLocalDepthTwoFiniteFlat).
- #1428 [weakened statement] Sheaf.Paper.CartierEquality: cartier_equality: [Algebra.FiniteType k K] with K a field forces K/k finite, so trdeg = 0 and the statement degenerates. Use finitely generated field extensions (IntermediateField.FG ⊤).
- #1428 [weakened statement] Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore: sectionRing_veronese_fraction_core concludes only Nonempty (_ ≃+ _): state bijectivity of the canonical map [n, xi] ↦ xi / s^n.
- #1428 [weakened statement] Sheaf.RingTheory.CompletedModuleAssociatedGradedGenerators: completedModule_associatedGraded_generators: the b witnesses are decoration (b j := mk (a j)) and completeness/Noetherianity are unused. State the associated-graded generation claim of the blueprint node.
- #1428 [padded statement] Sheaf.CategoryTheory.Sites.PresheafFreeExtLocalKilling: exists_presheaf_ext_local_killing_witness pads its conclusion with (∃ h : … = 0, True): remove the padding.
- #1428 [duplicate] Sheaf.AlgebraicGeometry.SheafZeroStalks: Scheme.Modules.isZero_of_isZero_stalks duplicates Scheme.Modules.isZero_of_isZero_stalk (upstream Cohomology/FiniteFibre.lean).
- #1428 [duplicate] Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker: Scheme.Hom.pic_proper_ntorsion_coker duplicates the second conjunct of Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient (upstream Curve/Jacobian.lean).
- #1428 [duplicate] Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties: finalBaseSystem_properties duplicates Scheme.noetherianBaseSystem_spec (upstream Compactification/FinitePresentation.lean); it follows from the fields of NoetherianApproximation.
- #1428 [duplicate] Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope: nagataFinitePresentationEnvelope duplicates Scheme.Hom.separatedFPEnvelope (upstream SeparatedEnvelope.lean) and picks an arbitrary start index via Classical.choice, unlike its docstring.
- #1428 [duplicate] Sheaf.Paper.VanishingDescendsRetract: vanishing_descends_retract duplicates Etale.isZero_homology_rightDerivedFunctorPlus_of_retract.
- #1428 [duplicate] Sheaf.Algebra.Homology.KInjectiveProducts: CochainComplex.termwise_product_isKInjective_and_isLimit duplicates CochainComplex.isKInjective_of_isLimitFan + DerivedCategory.isLimitFanMkQObjOfIsKInjective (upstream DerivedCategory/Products.lean).
- #1428 [duplicate] (module no longer in the library: StrictHenselizationCompatibility.lean): restates the existing AffinePointedEtaleNeighborhood.initial_ι instance and instances.
- #1428 [duplicate] Sheaf.RingTheory.ProjectiveResolutionExtDegree: projective-dimension cluster (projective_resolution_ext_degree, projective_of_projective_resolution_length_zero, hasProjectiveResolutionLE_of_shortExact_projective_middle, first conjunct of localization_preserves_projective_and_global_dimension) restates Mathlib hasProjectiveDimensionLT_iff, projective_iff_hasProjectiveDimensionLE_zero, ShortExact.hasProjectiveDimensionLT_X3, localizedModule_hasProjectiveDimensionLE.
- #1428 [duplicate] Sheaf.RingTheory.ZariskisMainAway: zariskisMainProperty_of_isQuasiFiniteAtPrime is the unfolded Algebra.ZariskisMainProperty; Scheme.Hom.IsQuasiFinite / IsLocallyQuasiFinite re-encode Mathlib LocallyQuasiFinite (locallyQuasiFinite_and_quasiCompact_iff).
- #1428 [duplicate] Sheaf.Topology.RingedModuleSkyscraper: SheafOfModules.RingedSkyscraperSections / ringedModuleSkyscraper are the same construction as Scheme.Modules.skyscraper (Modules/FlatPullbackStalk.lean): build one on the other.
- #1428 [duplicate] Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed: SheafOfModules.tensorClosed and exists_tensorHom_linearEquiv repackage SheafOfModules.monoidalClosed / tensorHomEquiv; first conjunct of homObj_isSheaf_and_sections is PresheafOfModules.isSheaf_homObj; tor_dimension_shift_free is tor_dimension_shift_natural without naturality; siteExtensionByZeroPresheaf is SheafOfModules.extensionByZeroPresheaf; first conjunct of grothendieckAbelian_with_localized_generator is SheafOfModules.isGrothendieckAbelian.
- #1428 [duplicate] Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf, Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf: equivariantModulePresheaf_isSheaf and equivariantModulePresheaf_restrictScalars_isSheaf are the same theorem proved twice from copy-pasted code: keep one.

## Full review texts

```
=== #1424 fuxi-bot
VERDICT: CHANGES REQUESTED

1. **22 new `sorry`s must be proved.** Every one is new relative to `slopmaster2`. Each lemma states either a `lem-weil-pbc-*` node from the same section as this PR (`sec-proper-base-change`, mostly `sk-thm-p1`/`sk-thm-properbasechange`) or a label that is absent from the blueprint (`new-tower-limit-*`, `lem-stage3-epi-over-functor`, `lem-pbc-additive-scalar-base-change`, …). None is a node of a different subsection, so all are blocking:
   - `CategoryTheory.tower_limit_exact_of_coordinate_maps` (TowerLimitExactCoordinateMaps.lean:25). It is **false as stated**: correct the statement first (item 2).
   - `CategoryTheory.tower_limit_induced_maps` (TowerLimitInducedMaps.lean:25). This is `limMap (NatTrans.ofOpSequence …)`. Prove it, or better replace it with that construction.
   - `extOne_directSum_bijective` (Algebra/ExtOneDirectSum.lean:61)
   - `exists_mapping_cylinder_split_factorization` (Algebra/Homology/MappingCylinderSplitFactorization.lean:51)
   - `Algebra.exists_limit_finite_presentation_core` (Algebra/LimitFinitePresentation/Core.lean:50)
   - `Ideal.eq_zero_of_annihilated_quotient_primaryComponent` (Algebra/Module/QuotientPrimaryComponentNoTorsion.lean:47)
   - `tor_one_change_of_rings_surjective` (Algebra/TorOneSurjectiveChangeRings.lean:68)
   - `prod_linearEquiv_of_twoTermHomotopy` (Algebra/TwoTermHomotopyEquivalenceDirectSum.lean:44)
   - `annihilator_subsheaf_quasicoherent` (AlgebraicGeometry/AnnihilatorQuasicoherent.lean:40)
   - `coherent_kernel_intersection_finiteType` (AlgebraicGeometry/CoherentKernelIntersectionFiniteType.lean:46)
   - `exists_constantGroupSchemeMultiplication` (AlgebraicGeometry/ConstantGroupScheme.lean:74). The data def `constantGroupSchemeMultiplication` (l.89) is `Classical.choose` of this sorry, so it is sorry-bodied data. Construct `m` directly: `Cover.glueMorphisms` on `openCoverOfLeftRight`, or `Sigma.desc` after identifying the fibre square with `∐ (E × E) T`. Then prove the two properties.
   - `exists_additive_scalar_base_change` (AlgebraicGeometry/Curve/AdditiveScalarBaseChange.lean:48)
   - `exists_artinSchreier_pullback_rows` (AlgebraicGeometry/Curve/ArtinSchreierPullbackRows.lean:41)
   - `normalization_comparison_on_iso_locus` (AlgebraicGeometry/Curve/NormalizationComparisonOnIsoLocus.lean:46)
   - `epi_overFunctor_map` (AlgebraicGeometry/EpiOverFunctor.lean:24)
   - `arrow_product_transitions_cocycle_of_projections` (CategoryTheory/ArrowProductTransitionsCocycleLaw.lean:23)
   - `exists_arrow_product_transitions` (CategoryTheory/ArrowProductTransitionsExistence.lean:24)
   - `exactFunctor_resolution_cocycle_hom` (CategoryTheory/ExactFunctorResolutionCocycle.lean:74)
   - `free_sheaf_flat` (CategoryTheory/GrothendieckAbelian/Monoidal/FreeSheafFlat.lean:73)
   - `siteCoverings_common_refinement` and `siteCoverings_finite_common_refinement` (CategoryTheory/SiteCoveringsCommonRefinement.lean:39, 67). Derive these from Mathlib's `ZeroHypercover.inter` / `PreZeroHypercover.interFst`/`interSnd` (Mathlib/CategoryTheory/Sites/Hypercover/Zero.lean). For arbitrary `IsPullback` squares, transport along `IsPullback.isoPullback`. Get the finite version by iterating `inter`.
   - `tower_split_envelope` (CategoryTheory/TowerSplitEnvelope.lean:59)

2. **False statement: `tower_limit_exact_of_coordinate_maps`.** Nothing says `α`/`β` commute with the transition maps, and `hU`/`hV` only constrain `U`/`V` on elements of the limit. Counterexample, with R a nontrivial ring:
   - Take `F_n = R` with zero transitions, so `lim F = 0`; `G_n = R` with identity transitions, so `lim G = R`; and `H = 0`.
   - Take `α n = id` and `β n = 0`. Every row is short exact.
   - Take `U = 0` and `V = 0`. Then `hU` and `hV` hold, but `Exact U V` fails because `ker V = R ≠ 0 = range U`.

   Fix: add the naturality hypotheses `hα`/`hβ` exactly as in `TowerLimitInducedMaps.lean` (or take natural transformations), then prove it.

3. **Duplicates of `slopmaster2`/Mathlib.** Remove each and use the existing declaration, re-pointing callers:
   - `Scheme.Hom.isIso_residueFieldMap_of_isClosedImmersion` (ClosedImmersionResidueFieldIso.lean:43). Its proof is literally `Hom.isIso_residueFieldMap i z`, which is on slopmaster2 (`ConstructibleSheaf/UniversalHomeomorphism.lean:61`).
   - `Abelian.Ext.exactFunctorCompositionComparison` (ExtExactFunctorCompositionComparison.lean:59). It has the same statement as `Abelian.Ext.mapExactFunctor_comp_mk₀_eq` (`WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean:117`), minus `[EnoughInjectives C]`. Generalise the existing lemma instead of adding a second one. `exactFunctorIdentityComparison` (ExtExactFunctorIdentityComparison.lean:58) is its `G₂ = 𝟭` case; derive it from `mapExactFunctor_eq_of_iso` + `mapExactFunctor_id`.
   - `mapExtendTermIso` / `mapExtendComplexIso` (MapExtendHomology.lean:21, 41) duplicate `HomologicalComplex.mapExtendX` / `mapExtendIso` (`FromJoel/Algebra/Homology/Embedding/ExtendMap.lean:32, 45`).
   - `tensorBicomplex` / `tensorBicomplexMap` (Algebra/Homology/TensorBicomplex.lean:33, 56) are Mathlib's `((Functor.mapBifunctorHomologicalComplex (curriedTensor _) _ _).obj P).obj Q` and its `map`.
   - `liftedCommGrpBranch` (Adjunction/LiftedCommGrpBranch.lean:36) only packages Mathlib's `Functor.mapCommGrp` / `Adjunction.mapCommGrp` inside an `∃`. Use those directly.

4. **Over-hypothesised, trivial statement: `derivedCategory_towerLimit_cone`** (Triangulated/DerivedLimitTowerCone.lean:34). `HasDerivedCategory`, `CountableAB4Star`, `hP`, `EnoughInjectives` and `IsKInjective` are all unused. The conclusion only says that a ℕᵒᵖ-diagram of complexes has a limit. Drop the unused hypotheses so the statement says what it proves.

**Non-blocking notes** (apply what is cheap):
- **Data behind `∃`/`Nonempty` where the proof builds a canonical object.** These should be `def`s plus lemmas: `disjointOpenExtension_biproduct_iso`, `exists_annihilator_subsheaf`, `constantRing_moduleSheaf_equivalence`, `adicTower_completedScalarLimit`, `changeIdealCompletion`, `mapExtendHomology_nonempty_iso`, `singleHomotopyPresheaf_homology`, `stage_section_functor_from_transitions`, `sheavesAbelianForward`, `finiteProductRingFunctor`, `exists_kernel_to_shifted_mappingCone_of_degreewise_epi`.
- **`exists_limit_finite_presentation_core` (Core.lean:61)** gives only `FiniteType (η.app l)`. The construction (and Stacks 00R0) gives `FinitePresentation`; consider strengthening it while proving.
- **Duplication within the PR:**
  - `siteCohomology_zero_section` (SiteCohomologyZeroSections.lean:25) has the same body as `Sheaf.objectCohomologyEval₀` (SiteCohomologyPullbackData.lean:34).
  - `DerivedCountableProductsProperties.lean` copies about 240 lines of private helpers from `DerivedCountableProductsCore.lean`, and has an unused `[HasCountableProducts …]`.
  - `ConstantModuleTransitionCoefficients.lean` copies private lemmas from `ConstantModulePushforwardFunctoriality.lean`.
  - `SiteCechComplex` overlaps Mathlib's `cechComplexFunctor` (Sites/SheafCohomology/Cech.lean).
- **`Scheme.Modules.IsAmple` (Ample.lean)** is the absolute Stacks 01PS notion, next to slopmaster2's `AlgebraicGeometry.IsAmple` (projective over a field). Cross-reference the two in the docstrings, and use `nonvanishingLocus` in `IsAmple`.
- **Unused hypotheses:**
  - `[Finite …]` in `constantEtaleSheaf_shortExact`
  - `_hT` in HorseshoeDefectFactorization.lean:60
  - `[IsFiltered J]` in ColimitSiteRawSectionDiagram
  - extra precoverage classes in `SiteCechComplex.exists_of_covering`
  - `_h₁` in `sheavesAlgebraicStructuresRing_morphism`
- **Naming:**
  - Theorems in lowerCamelCase should be snake_case: `compatiblePullbackSheafSystem`, `constantPullback*Coherence`, `powerReductionJI/IJ`, `changeIdealCompletion*`, `finiteProductRingFunctor`, `liftedCommGrpBranch`, `ring(Co)adjunctPreservesOperations`, `cartesianScalarDistributivityTransport`, `exactFunctor*Comparison`, `identityDerivedHomologyComparison`, `sheavesAbelianForward`, `transportScalarActionDiagrams`.
  - Type-valued abbrevs `zigzagTotal`/`zigzagModule` should be UpperCamelCase.
  - `@[instance] theorem` in SiteCechComplex.lean:389/408/426 should be `instance`.
- **Docs:**
  - Several files lack a module docstring.
  - Category-theory square/naturality lemmas (horseshoe, Ext comparisons, constant-pullback coherence, the right-derived cube) lack a commutative diagram.
  - Many cited blueprint labels are not in the blueprint.
- **Lines over 100 characters:** DerivedCountableProducts{Core,Properties}.lean:91, StageSectionFunctorFromTransitions.lean:205, TriangleMorphismExtension.lean:99/114.
- **PR description:** it names no key theorems or definitions.
=== #1428 fuxi-bot
VERDICT: CHANGES REQUESTED

Scope: this reviews the part-3 content, i.e. the diff `pr1427 head (077cd8b9)..29b541ac` (716 new files, ~96k lines, plus the proof of `Etale.isZero_of_isZero_lowerStar_obj`). Parts 1–2 are covered by #1424 / #1427. There are no maintainer comments and no earlier reviews on this PR.

**Blocking**

1. **Three `sorry`'d statements are false. Fix the statement first, then prove it.**
   - `Topology/SetsExtensionByEmptyAdjunction.lean:37` `extensionByEmpty_adjunction_stalks`: the first conjunct `extensionByEmptyPresheaf U ⊣ (pullback ⋙ presheafToSheaf)` is false.
     - Counterexample: take U = ⊤. The statement then says sheaf inclusion is left adjoint to sheafification, which has the adjunction the wrong way round. Concretely, on discrete X = {a,b} take G = terminal sheaf and F with F(X) = ∅ and F = 1 on the other opens. Then Hom(G,F) = ∅ but Hom(G, aF) = 1.
     - Fix: drop the conjunct, or use plain presheaf restriction as the right adjoint.
   - `AlgebraicGeometry/Modules/DeterminantSplitComparisonLocal.lean:53` `determinant_split_comparison_restriction`: `c` is unconstrained, so `hd` does not force `d` to commute with restriction.
     - Counterexample: X = Spec ℤ, r₁ = 0, r₂ = r₃ = 1, X₂ = X₃ = 𝒪, g = id. Rescale `d W` and `c W` by −1 on every W ≠ V.
     - Fix: require g ∘ c = id (or prove naturality together with the existence in the `_local` lemma).
   - `AlgebraicGeometry/Morphisms/StalkNormalizationDepthTwoSectionFlatCore.lean:41` `stalk_normalization_depth_two_section_flat_core`: the file's own comment (lines 22–30) gives the counterexample A = ℚ[x²,xy,y²] with U = the punctured cone. The missing hypothesis is the rational-point / dense-fibre condition of Tag 0EYJ, cf. `hclosed` in `SmoothLocalDepthTwoFiniteFlat`. Add it.

2. **Weakened or trivialised statements. Restate them faithfully.**
   - `Paper/CartierEquality.lean:50` `cartier_equality`: `[Algebra.FiniteType k K]` with K a field forces K/k finite (Zariski), so trdeg = 0 and the Cartier equality degenerates. Use finitely generated *field* extensions (`IntermediateField.FG ⊤`).
   - `AlgebraicGeometry/SectionRingVeroneseFractionsCore.lean:26` `sectionRing_veronese_fraction_core`: concludes only `Nonempty (_ ≃+ _)`. State bijectivity of the canonical map `[n, ξ] ↦ ξ / sⁿ`.
   - `RingTheory/CompletedModuleAssociatedGradedGenerators.lean:64` `completedModule_associatedGraded_generators`: the `b` witnesses are decoration (`b j := mk (a j)`), and what remains never uses completeness or Noetherianity. State the associated-graded generation claim of the blueprint node.
   - `CategoryTheory/Sites/PresheafFreeExtLocalKilling.lean:214` `exists_presheaf_ext_local_killing_witness`: the conclusion is padded with `∃ h : … = 0, True`. Remove the padding; the theorem at line 234 already states the content.

3. **New `sorry`s: all ~99 are blocking.**
   - Every `sorry`-proved declaration in part 3 is new.
   - The blueprint id each one cites is either absent from the blueprint, or is a `sec-proper-base-change` node (the PR's own section) that the lemma does not state exactly.
   - The only one citing another section's node is `finalBaseSystem_properties` (Nagata). It duplicates the existing `Scheme.noetherianBaseSystem_spec` (`Compactification/FinitePresentation.lean:150`) and follows from the fields of `NoetherianApproximation`: `isNoetherian_obj`, `locallyOfFiniteType_obj`, `compactSpace_obj`, `isAffineHom_map`, and `isLimit` for the comparison iso.
   - Prove each of these. Several close in a few lines from existing results:
     - `koszul_differential_square_zero`: `CliffordAlgebra.contractLeft_contractLeft`.
     - `away_map_functorial`: `IsLocalizedModule.map_comp'`, `map_id`, `map_add`.
     - `isReduced_tensorProduct_of_finiteSeparable`: `Algebra.FormallyUnramified.of_isSeparable`, then base change, then `FormallyUnramified.isReduced_of_field`.
     - `krull_intersection_localization`: `Ideal.mem_iInf_smul_pow_eq_bot_iff`.
     - `locallyOfFiniteType_of_fpqcCover`: Mathlib's `DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, as in `UniversallyClosedOfFpqcCover`.
     - `isAffineHom_of_fpqc_cover`: `of_isPullback_of_ofArrows_mem_fpqcTopology` with `IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact`.
     - `lft_over_field_isolated_point_residue_finite`: `Hom.finite_residueField_of_isClosed` plus Jacobson.
     - `vanishing_descends_retract`: transfer the `IsSplitMono` argument of `Etale.isZero_homology_rightDerivedFunctorPlus_of_retract`.
     - `essentiallyConstant_splitting` and `essentiallyConstantInd_hom_colimit_bijective`: elementary.
     - `stalk_isFiniteFree_of_isFiniteLocallyFree`: reuse the private `localStalkEquiv` in `FiniteLocallyFreeStalkFinrank.lean`.
     - `localizedSModule_properties`, `swap_properties`, `compare_properties`: `choose_spec` of the existing `exists_*` lemmas.
   - Full list: `exists_differentials_on_graded_model_of_directed_colimit`; `affine_perfect_chainMap_descent`; `affine_perfect_homotopy_descent`; `acyclic_homComplex_of_boundedAbove_finiteFree`; `exists_finite_projective_graded_model_of_directed_colimit`; `homTensorDegreewise_exists`; `localizedHomComplex_nullHomotopy_iff_boundary`; `localizedHomComplex_cycles_bijective`; `quasiIso_homComplex_map_of_single_degree_exact_term`; `exists_homComplex_stupid_tail_shortExact`; `locallyFreeCharpoly_spec`; `locallyFree_constantRank_eq`; `Ideal.primaryComponent_baseChange_bijective`; `annihilator_stalk_local_lift`; `associatedModuleHom_injective`; `associatedModuleHom_surjective`; `baseChange_open_injective_coefficient_eq_zero`; `exists_changeOfRings_tensor_action_maps_actions`; `exists_changeOfRings_tensor_presheaf_map`; `exists_cechCoverRelativeEffacement_core`; `derivedSquareIso_commShift`; `derivedSquareIsoPasting`; `etale_coefficient_injective_system_embedding`; `finalBaseSystem_properties`; `exists_local_free_stalk_map_of_nonempty`; `isAffineHom_of_fpqc_cover`; `exists_geometric_generic_cover_model`; `higherDirectImageRawTransition_toHom`; `higher_direct_image_transition_core_composition`; `lft_over_field_isolated_point_residue_finite`; `determinant_split_comparison_local`; `determinant_split_comparison_restriction`; `exteriorSheaf_rank_wedge_eq_zero`; `exteriorTensor_kernel_eq_zero_of_relations`; `depth_two_pushforward_coherence`; `depth_two_of_finite_structure_algebra`; `formallyUnramified_of_flat_depth_two_finite_extension`; `locallyOfFiniteType_of_fpqcCover`; `flat_of_smooth_local_depth_two_finite_extension`; `stalk_normalization_depth_two_section_flat_core`; `isColimit_stalk_mapCocone`; `projectiveLine_twist_coherent_powers`; `relativeDifferentials_affine_sections_map_injective`; `relativeDifferentials_affine_sections_map_surjective`; `exists_restricted_affine_complex_system`; `sectionRing_chart_cross_multiplication`; `sectionRing_coefficient_arithmetic_of_numerator`; `sectionRing_second_chart_generator`; `sectionRing_veronese_fraction_core`; `smooth_differentials_free_rank_fibre_dimension`; `stalk_isFiniteFree_of_isFiniteLocallyFree`; `isIso_derivedBaseChangeMapPlus_torsion_assembly`; `colimit_site_abelian_pairwise_eventual_matching`; `colimit_site_finite_section_eventual_zero`; `raw_section_kan_unit_relations`; `colimit_site_raw_finite_equality_stabilization`; `colimit_site_raw_finite_sections_lift`; `colimit_stage_kan_cocone`; `compact_factorThrough_thickClosure`; `essentiallyConstantInd_hom_colimit_bijective`; `essentiallyConstant_splitting`; `first_quadrant_row_collapse`; `rightDerivedPlusSingleUnit_shift_transport`; `plus_construction_presheaf`; `exists_completeIntersection_subalgebra`; `isReduced_tensorProduct_of_finiteSeparable`; `cartier_equality`; `exists_surjective_tensorProduct_map_of_surjective`; `locallyConstantMapsPresheaf_hom_bijective`; `compare_properties`; `away_map_functorial`; `localizedSModule_properties`; `swap_properties`; `koszul_differential_square_zero`; `site_module_sheafification_lift_injective`; `vanishing_descends_retract`; `exists_artinian_coefficient_descent`; `exists_associatedGraded_ideal_approximation`; `basis_iff_basisQuotient_of_nilpotent`; `exists_map_of_finitePresentation_colimit`; `completedModule_associatedGraded_generators`; `conormalModule_principalLocalization`; `extension_descends_of_summands`; `directedUnionSubrings_flat_module`; `finiteType_and_isQuasiFiniteAtPrime_of_etale`; `exists_etale_finiteFactor_decomposition`; `length_quotSMulTop_lt_top_of_ringKrullDim_eq_one`; `localizedModule_atPrime_of_flat`; `formallySmoothAdic_of_flat_closedFiber_complete`; `krull_intersection_localization`; `exists_popescu_admissible_quotient_basis`; `isRegular_and_flat_quotient_of_closedFiber`; `exists_bounded_local_kernel_generators`; `tor_quotient_pow_strictly_pro_zero`; `exists_shortExact_projective_middle_of_wellOrderedUnion_succ`; `extensionByEmpty_adjunction_stalks`; `sheaves_injective_directedColimit_sections`; `exists_directed_inverseLimit_finite_sober`; `isCompact_limit_constructibleClosed`; `exists_compatible_point_of_spectral_constructible_closed`.

4. **Duplicates of `slopmaster2`, Mathlib or parts 1–2. Replace each with (or derive it from) the existing declaration.**
   - `Scheme.Modules.isZero_of_isZero_stalks` (`SheafZeroStalks.lean:40`) duplicates `Scheme.Modules.isZero_of_isZero_stalk` (`Cohomology/FiniteFibre.lean:102`).
   - `Scheme.Hom.pic_proper_ntorsion_coker` duplicates the second conjunct of `Scheme.nonempty_addEquiv_torsionBy_pic_and_quotient` (`Curve/Jacobian.lean:96`).
   - `finalBaseSystem_properties` duplicates `Scheme.noetherianBaseSystem_spec`.
   - `nagataFinitePresentationEnvelope` duplicates `Scheme.Hom.separatedFPEnvelope` (`SeparatedEnvelope.lean`). It also picks an arbitrary start index via `Classical.choice`, unlike its docstring.
   - `vanishing_descends_retract` duplicates `Etale.isZero_homology_rightDerivedFunctorPlus_of_retract`.
   - `CochainComplex.termwise_product_isKInjective_and_isLimit` (`KInjectiveProducts.lean:124`) duplicates `CochainComplex.isKInjective_of_isLimitFan` + `DerivedCategory.isLimitFanMkQObjOfIsKInjective` (`DerivedCategory/Products.lean`).
   - `StrictHenselizationCompatibility.lean:31,48` restates the existing `AffinePointedEtaleNeighborhood.initial_ι` instance and instances.
   - Projective-dimension cluster: `projective_resolution_ext_degree`, `projective_of_projective_resolution_length_zero`, `hasProjectiveResolutionLE_of_shortExact_projective_middle`, and the first conjunct of `localization_preserves_projective_and_global_dimension` restate Mathlib's `hasProjectiveDimensionLT_iff`, `projective_iff_hasProjectiveDimensionLE_zero`, `ShortExact.hasProjectiveDimensionLT_X₃` and `localizedModule_hasProjectiveDimensionLE`.
   - `zariskisMainProperty_of_isQuasiFiniteAtPrime` is literally the unfolded `Algebra.ZariskisMainProperty` (proof calls `ZariskisMainProperty.of_finiteType`). `Scheme.Hom.IsQuasiFinite` / `IsLocallyQuasiFinite` re-encode Mathlib's `LocallyQuasiFinite` ∧ finite-type conditions (`locallyQuasiFinite_and_quasiCompact_iff`).
   - Skyscraper module sheaf: `SheafOfModules.RingedSkyscraperSections` / `ringedModuleSkyscraper` (`Topology/RingedModuleSkyscraper.lean`) are the same construction as `Scheme.Modules.skyscraper` (`Modules/FlatPullbackStalk.lean`). Build one on the other.
   - Repackagings of pr1427 declarations:
     - `SheafOfModules.tensorClosed` and `exists_tensorHom_linearEquiv` repackage `SheafOfModules.monoidalClosed` / `tensorHomEquiv`.
     - The first conjunct of `homObj_isSheaf_and_sections` is `PresheafOfModules.isSheaf_homObj`.
     - `tor_dimension_shift_free` is `tor_dimension_shift_natural` with naturality dropped.
     - `siteExtensionByZeroPresheaf` is `SheafOfModules.extensionByZeroPresheaf` (their agreement is proved by `rfl`).
     - The first conjunct of `grothendieckAbelian_with_localized_generator` is `SheafOfModules.isGrothendieckAbelian`.
   - Same theorem proved twice from copy-pasted code: `equivariantModulePresheaf_isSheaf` and `equivariantModulePresheaf_restrictScalars_isSheaf`.

**Non-blocking**

- `exists_restricted_affine_complex_system` existentially quantifies almost everything (B is not required to be a colimit), so check that it still serves its call site. `derivedModuleFiltrationTelescope` does not tie `a`, `b` to `1 − shift` / `ι n`, as its docstring claims.
- The new top-level folder `WeilConjectures/Paper/` (34 files) is not a topic folder. Move its files to `RingTheory/`, `AlgebraicGeometry/` etc.
- Several theorem names are not Mathlib style: snake-case bundles like `*_properties` and `exists_*_core`.
- Several docstrings cite labels that don't exist in the blueprint (e.g. `new-determinant-split-restriction` and most `lem-pc-*` / `lem-sc-*` ids).
- The proof of `Etale.isZero_of_isZero_lowerStar_obj` (the only modified existing file) is fine.
```
