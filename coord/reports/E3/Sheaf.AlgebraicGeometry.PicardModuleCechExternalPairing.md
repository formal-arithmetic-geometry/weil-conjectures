## What changed

Repaired both returned modules in the sandbox, preserving their theorem types by
unfolding definitions. Removed their public import of
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree`; the external coordinate
hypothesis is its exact defining formula with the definitionally identical
`n2CupFront` and `n2CupBack`. The ordinary cochain formula uses
`n2CechCupCochain`, definitionally equal to `cechCupCochain`.

In `PicardModuleCechExternalPairing`, expanded `IsModuleCupProduct` to its exact
resolution characterization and replaced the private comparison proof's use of
`cechCup_resolution_representatives` with a complete proof from
`exists_cupCechResolutionComparison` and `cupCech_signed_axis_pairing`. Lift the
factor comparison classes through the surjective resolution class maps, form the
paired cycle by Leibniz, and compare its class with the Cech class through the
alpha/beta equations and the target comparison isomorphism. The prescribed cup
characterization and the original refinement squares finish the original theorem.
No dependency module, tool, target, or data construction is changed.

Return points repaired: both modules now pass the exact non-module global
batch-probe import pattern. It prints SHEAF-PROBED for both modules and no
SHEAF-AXIOM or SHEAF-SORRY. The old signatures, including both original named
predicates and cechCupCochain, compile as examples proved by the repaired
declarations. Thus the expanded signatures retain the old types by definitional
equality. Both modules compile cleanly together (34.2 and 27.3 seconds); the
batch reproduction takes 2.3 seconds and the original-signature checks 11.9 seconds.
All checks use lcompile.py with its unchanged 60-second limit. The reproduced
original baseline collision is retained in scratchpad/BaselineLegacy.lean.

## Proved and sorry left

`AlgebraicGeometry.Scheme.Modules.picardModuleCech_externalPairing`
(lem-sc-picard-module-cech-external-pairing) has a complete proof: the assigned
original hole remains closed.
`AlgebraicGeometry.Scheme.Modules.picardExternalCech_moduleRepresentatives`
(lem-sc-picard-external-cech-module-representatives) is also completely proved.
No direct sorry remains in either module. No holes are added or split off.
This is a repair/restoration of two returned proofs; the refreshed repository
has withdrawn both modules, so it is not a claim of two fresh net hole closures.
The existing dependencies of the resolution comparisons retain their own proof
status; this delivery adds no axioms or arbitrary witness constructions.

## No longer needed

The removed old direct proof dependencies are exactly
`lem-sc-picard-external-cech-cup-bidegree`, `def-sc-cech-cup-product`, and
`lem-sc-cech-cup-resolution-representatives`. Their notions remain in the
statements through definitionally identical formulas; their proof results are unused.

Removed direct public imports of
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` from both modules, and
removed the pairing module's proof import of
`Sheaf.Paper.CechCupResolutionRepresentatives`.
The external bidegree existence theorem is not needed: its prescribed coordinate
predicate is unfolded. The full Cech cup product and module cup existence and
invariance proofs are not needed: the statement assumes a cup satisfying its
resolution characterization. Only that exact characterization is unfolded.
The Cech-resolution-representatives hole is avoided by the direct alpha/beta
argument, using its existing comparison-existence and signed-axis components.

The following Sheaf modules leave this item's source import closure compared
with the returned two-module proof (not a claim that other targets cease to use
them). Their recorded nodes are listed when available. Mathematical notions in
unfolded hypotheses remain unchanged even when their original modules are absent.
No blueprint unit or realized unit step is bypassed; the unit record has no
realized nodes. The source import traversal is recorded in
scratchpad/pruned-import-closure.json and scratchpad/repaired-import-closure.json.

- `Sheaf.Algebra.Category.ModuleCat.CocontinuousGenerator` — `lem-sc-modulecat-cocontinuous-generator`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension` — `lem-pc-sites-module-sheafification-bilinear-extension`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence` — `lem-pc-sites-module-sheafification-bilinear-extension-existence`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness` — `lem-pc-sites-module-sheafification-bilinear-extension-uniqueness`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat` — `lem-pc-sites-modules-sheafification-flat`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor` — `lem-pc-sites-module-sheafification-tensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat` — `lem-pc-sites-modules-j-shriek-flat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` — `def-pc-flat-sheaf-modules`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct` — `lem-pc-sites-modules-coproduct-flat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` — `lem-pc-sites-sheaf-tensor-bilinear-universal`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor` — `lem-pur-acyclic-kflat-tensor-arbitrary`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` — `lem-pc-bounded-above-flat-kflat-site`
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic` — `lem-pc-bounded-above-flat-tensor-acyclic`
- `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree` — `lem-pc-bounded-above-flat-tensor-acyclic-degree`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement` — `lem-pc-kflat-bounded-flat-replacement`
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat` — `lem-pur-change-of-rings-acyclic-kflat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso` — `lem-pur-change-of-rings-kflat-quasi-iso`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorAcyclic` — `lem-pur-change-of-rings-tensor-acyclic`
- `Sheaf.Algebra.Homology.ChangeOfRingsTensorComparison` — `lem-pur-change-of-rings-tensor-comparison`
- `Sheaf.Algebra.Homology.CyclePullbackCore` — `lem-pc-functorial-cycle-pullback-core-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackLaws` — `lem-pc-cycle-pullback-tower-laws-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackLifting` — `lem-pc-functorial-cycle-pullback-lifting-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackResolution` — `lem-pc-functorial-cycle-pullback-construction`
- `Sheaf.Algebra.Homology.CyclePullbackTower` — `def-pc-cycle-pullback-tower-data-stage3`
- `Sheaf.Algebra.Homology.CyclePullbackTowerComparison` — `lem-pc-cycle-pullback-tower-comparison-stage3`, `new-tower-comparison-second`, `def-tower-canonical-comparison-g3`, `new-tower-comparison-first`
- `Sheaf.Algebra.Homology.DerivedInternalHom` — `def-pur-derived-internal-hom`
- `Sheaf.Algebra.Homology.FilteredColimitsTensor` — `lem-pc-module-filtered-colimits-tensor`
- `Sheaf.Algebra.Homology.FilteredColimitsTensorTotal` — `lem-pc-module-filtered-colimits-tensor-preserves`
- `Sheaf.Algebra.Homology.FlatAugmentationEpicification` — `lem-pc-flat-augmentation-epicification`
- `Sheaf.Algebra.Homology.FlatCoverFunctor` — `lem-pc-sites-modules-functorial-flat-cover`
- `Sheaf.Algebra.Homology.FlatTruncationSuccessor` — `lem-pc-flat-truncation-successor`
- `Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison` — `lem-pc-flat-truncation-telescope-comparison`
- `Sheaf.Algebra.Homology.FlatTruncationTower` — `lem-pc-flat-truncation-tower`
- `Sheaf.Algebra.Homology.HomComplex` — `def-pur-hom-complex`
- `Sheaf.Algebra.Homology.HomComplexSectionsCanonicalComparison` — `lem-pur-hom-complex-sections-canonical-comparison`
- `Sheaf.Algebra.Homology.HomComplexSectionsCochains` — `lem-pur-hom-complex-sections-cochains`
- `Sheaf.Algebra.Homology.HomComplexSectionsCochainsComm` — `lem-pur-hom-complex-sections-cochains-comm`
- `Sheaf.Algebra.Homology.HomComplexSectionsDerivedNaturality` — `lem-pur-hom-complex-sections-derived-naturality`
- `Sheaf.Algebra.Homology.HomComplexSectionsHomotopyNaturality` — `lem-pur-hom-complex-sections-homotopy-naturality`
- `Sheaf.Algebra.Homology.HomComplexSectionsQuasiIso` — `lem-pur-hom-complex-sections-quasi-iso`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransport` — `lem-pc-ringed-inverse-image-stalk-scalar-transport`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportBeta` — `lem-pc-ringed-inverse-image-stalk-scalar-transport-beta`
- `Sheaf.Algebra.Homology.InverseImageStalkScalarTransportNaturality` — `lem-pc-ringed-inverse-image-stalk-scalar-transport-naturality`
- `Sheaf.Algebra.Homology.KFlat` — `def-pc-kflat-complex`
- `Sheaf.Algebra.Homology.KFlatClosure` — `lem-pc-kflat-cone-direct-sum`
- `Sheaf.Algebra.Homology.KFlatModuleBaseChange` — `lem-pc-kflat-extension-of-scalars`
- `Sheaf.Algebra.Homology.KFlatPullback` — `lem-pc-kflat-pullback-preservation`
- `Sheaf.Algebra.Homology.KFlatResolution` — `lem-pc-kflat-resolution`
- `Sheaf.Algebra.Homology.KFlatStalkCriterion` — `lem-pc-kflat-stalk-criterion`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure` — `lem-pc-kflat-closure`
- `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree` — `lem-pc-kflat-tensor-cone-two-out-of-three`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized` — `lem-pur-kinjective-restrict-localized`
- `Sheaf.Algebra.Homology.LocalizedHomComplexBoundaries` — `lem-pur-localized-hom-complex-boundaries`
- `Sheaf.Algebra.Homology.LocalizedHomComplexCycleLift` — `lem-pur-localized-hom-complex-cycle-lift`
- `Sheaf.Algebra.Homology.LocalizedHomComplexCycles` — `lem-pur-localized-hom-complex-cycles-aux`
- `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesBijective` — `lem-pur-localized-hom-complex-cycles-bijective`
- `Sheaf.Algebra.Homology.LocalizedHomComplexCyclesForward` — `lem-pur-localized-hom-complex-cycles-forward`
- `Sheaf.Algebra.Homology.LocalizedHomComplexHomology` — `lem-pur-localized-hom-complex-homology-aux`
- `Sheaf.Algebra.Homology.LocalizedHomComplexHomotopy` — `lem-pur-localized-hom-complex-homotopy`
- `Sheaf.Algebra.Homology.LocalizedModuleRestrictionQuasiIso` — `lem-pur-localized-module-restriction-quasi-iso`
- `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction` — `lem-pur-kinjective-restrict-localized-adjunction`
- `Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists` — `new-localized-restriction-extension-exists`
- `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap` — `lem-pur-rhom-well-defined`
- `Sheaf.Algebra.Homology.QuasiIsoOfSections` — `lem-pur-quasi-iso-of-sections`
- `Sheaf.Algebra.Homology.RelativeFlatExtension` — `lem-pc-relative-flat-extension`
- `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal` — `lem-pur-rhom-into-kinjective-local`
- `Sheaf.Algebra.Homology.StalkTensorComplex` — `lem-pc-stalk-tensor-complex`
- `Sheaf.Algebra.Homology.StalkTensorComplexDegrees` — `lem-pc-stalk-tensor-complex-degrees`
- `Sheaf.Algebra.Homology.StalkTensorComplexDifferential` — `lem-pc-stalk-tensor-complex-differential`
- `Sheaf.Algebra.Homology.TelescopeColimit` — `lem-pc-complex-hocolim-colimit`
- `Sheaf.Algebra.Homology.TelescopeShiftMono` — `lem-pc-telescope-shift-mono`
- `Sheaf.Algebra.Homology.TensorPullbackStalkComplex` — `lem-pc-tensor-pullback-stalk-complex`
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalars` — `lem-pc-tensor-restrict-extend-scalars`
- `Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule` — `lem-pc-tensor-restrict-extend-module-natural`
- `Sheaf.Algebra.Homology.TruncationTelescope` — `lem-pc-kflat-hocolim-truncations`
- `Sheaf.AlgebraicGeometry.DerivedCategory` — `def-pc-derived-category`
- `Sheaf.AlgebraicGeometry.DerivedTensorStructure` — `def-pc-scheme-derived-tensor-structure`
- `Sheaf.AlgebraicGeometry.GlobalDerivedHom` — `def-pc-global-derived-rhom`
- `Sheaf.AlgebraicGeometry.InverseImageModuleFunctor` — `lem-pc-inverse-image-module-functor-exact`
- `Sheaf.AlgebraicGeometry.InverseImageTensorPullbackComparison` — `lem-pc-inverse-image-tensor-pullback-comparison`
- `Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` — `lem-sc-picard-external-cech-cup-bidegree`
- `Sheaf.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived` — `lem-pc-ringed-space-tensor-pullback-underived`
- `Sheaf.AlgebraicGeometry.SchemeModuleFreeYonedaIso` — `lem-pc-scheme-module-free-yoneda-iso`
- `Sheaf.Paper.CechCupProduct` — `def-sc-cech-cup-product`
- `Sheaf.Paper.CechCupResolutionRepresentatives` — `lem-sc-cech-cup-resolution-representatives`
- `Sheaf.Paper.GlobalSectionsLaxMonoidalData` — `lem-sc-global-sections-lax-monoidal-data`
- `Sheaf.Paper.GlobalTensorPullbackDerivedData` — `lem-sc-global-tensor-pullback-derived-data`
- `Sheaf.Paper.GlobalTensorPullbackKFlat` — `lem-sc-global-tensor-pullback-kflat`
- `Sheaf.Paper.GlobalTensorPullbackMatesIsIso` — `lem-sc-global-tensor-pullback-mates-isiso`
- `Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization` — `lem-sc-global-tensor-pullback-monoidal-normalization`
- `Sheaf.Paper.GlobalTensorPullbackOplaxIsIso` — `lem-sc-global-tensor-pullback-oplax-isiso`
- `Sheaf.Paper.GlobalTensorPullbackTensorDescent` — `lem-sc-global-tensor-pullback-tensor-descent`
- `Sheaf.Paper.GlobalTensorPullbackUnderivedData` — `lem-sc-global-tensor-pullback-underived-data`
- `Sheaf.Paper.ModuleCohomologyCupProduct` — `def-sc-module-cohomology-cup-product`
- `Sheaf.Paper.ModuleCupAdjunctionCalculation` — `lem-sc-module-cup-polygon-calculation`
- `Sheaf.Paper.ModuleCupAdjunctionPolygon` — `lem-sc-module-cup-adjunction-polygon`
- `Sheaf.Paper.ModuleCupCanonicalHZeroIdentification` — `lem-sc-module-cup-canonical-hzero-identification`
- `Sheaf.Paper.ModuleCupCochainComparisonSquares` — `lem-sc-module-cup-cochain-comparison-squares`, `def-sc-module-cup-cochain-pullback-comparison`
- `Sheaf.Paper.ModuleCupCochainCounitTensor` — `lem-sc-module-cup-cochain-counit-tensor`
- `Sheaf.Paper.ModuleCupComponentChainEquation` — `lem-sc-module-cup-resolution-chain-equation`
- `Sheaf.Paper.ModuleCupComponentSectionMap` — `lem-sc-module-cup-resolution-section-map`
- `Sheaf.Paper.ModuleCupDerivedTensorConnectivity` — `lem-sc-module-cup-derived-tensor-connectivity`
- `Sheaf.Paper.ModuleCupEqualDerivedMapsClass` — `lem-sc-module-cup-equal-derived-maps-class`
- `Sheaf.Paper.ModuleCupGlobalCounitComparison` — `lem-sc-module-cup-global-counit-comparison`
- `Sheaf.Paper.ModuleCupGlobalTensorComparison` — `lem-sc-module-cup-global-tensor-comparison`
- `Sheaf.Paper.ModuleCupGlobalTensorPullback` — `lem-sc-module-cup-global-tensor-pullback`
- `Sheaf.Paper.ModuleCupHZeroIdentification` — `lem-sc-module-cup-hzero-identification`
- `Sheaf.Paper.ModuleCupKInjectiveTarget` — `lem-sc-module-cup-kinjective-target`
- `Sheaf.Paper.ModuleCupNaiveDerivedCompatibility` — `lem-sc-module-cup-naive-derived-compatibility`
- `Sheaf.Paper.ModuleCupNaiveMap` — `lem-sc-module-cup-naive-map-chain`
- `Sheaf.Paper.ModuleCupPairingExists` — `lem-sc-module-cup-pairing-exists`
- `Sheaf.Paper.ModuleCupRealizationComplexData` — `def-sc-module-cup-realization-complex-data`
- `Sheaf.Paper.ModuleCupRealizationEvaluation` — `lem-sc-module-cup-realization-evaluation`
- `Sheaf.Paper.ModuleCupResolutionAugmentation` — `lem-sc-module-cup-resolution-augmentation`
- `Sheaf.Paper.ModuleCupResolutionExistence` — `lem-sc-module-cup-resolution-components`, `lem-sc-module-cup-resolution-existence`
- `Sheaf.Paper.ModuleCupResolutionInvariance` — `lem-sc-module-cup-resolution-invariance`
- `Sheaf.Paper.ModuleCupResolutionRealization` — `lem-sc-module-cup-resolution-realization`
- `Sheaf.Paper.PointInverseEvaluationKFlat` — `lem-sc-point-inverse-evaluation-kflat`
- `Sheaf.Topology.PointModuleEvaluationEquivalence` — `lem-pc-point-module-evaluation-equivalence`
- `Sheaf.Topology.RingedModuleSkyscraper` — `def-pc-ringed-module-skyscraper`
- `Sheaf.Topology.SkyscraperComplex` — `lem-pc-skyscraper-complex`
- `Sheaf.Topology.SkyscraperComplexAcyclic` — `lem-pc-skyscraper-complex-acyclic`
- `Sheaf.Topology.SkyscraperComplexStalk` — `lem-pc-skyscraper-complex-stalk-recovery`

## Where the brief, the DAG or earlier work was wrong

The earlier diagnosis correctly located the anonymous local-instance collision,
but incorrectly concluded that the unheld dependency modules must be renamed.
The collision is avoided entirely within the returned modules: unfold the two
predicates, use the existing lightweight tuple formula, and prove the comparison
from existing alpha/beta components. Both theorem types remain definitionally
identical. No forced adaptation outside the assigned/restored modules is necessary.
The old DAG route used a representatives theorem with the heavy full cup import;
the repaired route records the existing comparison-existence and signed-axis nodes.

## New nodes

No new node or new sorry is introduced by this repair. The two nodes supplied
in the repair sandbox are restored with the modules:
`lem-sc-picard-external-cech-module-representatives` records the proved cycle
transport and tuple equality, and `lem-sc-picard-module-cech-external-pairing`
records the proved module comparison. Their lean.statement fields
record the expanded signatures verbatim; their statements in words are unchanged.
The representatives node now uses `new-cup-cech-product-core` and no longer
uses the bidegree-existence or full Cech-product proof nodes; the external
coordinate hypothesis is expanded directly. The pairing node's proof dependencies replace
lem-sc-cech-cup-resolution-representatives with
lem-sc-cech-cup-resolution-comparison-exists and
lem-sc-cech-cup-signed-axis-pairing.
Change record: coord/changes/picard-module-cech-external-pairing-restore.md.


## Second reading by E3

1. Interface: PASS. Both modules and both nodes are absent from the read-only
   repository, as stated in the restoration record. Compared each module with
   the exact returned version in scratchpad/Original*.lean.txt and the original
   node records in repair.diff. The only public signature edits are the declared
   unfoldings of IsPicardExternalCechCupBidegree and IsModuleCupProduct and the
   definitionally identical n2CechCupCochain. Read the original definitions and
   checked the old signatures with the repaired modules loaded from this
   sandbox's .lbuild. Both examples compile (11.3 seconds). No hypothesis,
   conclusion, coefficient object or target is changed. No current repository
   source imports either withdrawn module; the restored helper's consumer is
   delivered together. Public imports supply exposed signatures; the resolution
   comparisons, signed-axis theorem, refinement squares and quasi-coherent
   pullback import are proof-only imports.

2. Proof: PASS. Compiled the two modules in import order with lcompile.py --all
   (37.6 and 28.1 seconds), without warnings. Neither has a direct sorry or a
   forbidden declaration/attribute. Inspected every private construction: cycles
   are transported through actual cochain maps and additive isomorphisms, not
   chosen from an unproved existence statement. The existing adjunction choice
   has its unit pinned sectionwise by exists_tensorPullbackAdjunction, and this
   theorem is proved. The original non-module batch probe, explicitly loaded
   against the sandbox overlay, prints SHEAF-PROBED for both modules and no
   SHEAF-SORRY or SHEAF-AXIOM. #print axioms of the representatives theorem lists
   propext, Classical.choice and Quot.sound; the pairing theorem also lists
   sorryAx from existing imported dependencies. Thus its local hole is closed
   but the pairing is not yet an axiom-free target proof.

3. Split statements: PASS. Zero new holes and zero split-off statements. The two
   restored public statements express genuine cycle transport and comparison,
   not a restatement left admitted. Checked degree zero (the shared vertex),
   p = 0 or q = 0, empty indexing families, zero inputs and zero coefficients:
   the same finite-tuple restrictions and quotient maps apply, with no positivity,
   nonempty-cover or affine-cover assumption added. Searched with leanfinder for
   cycle-to-homology quotient surjectivity and rg for other cup comparison routes.
   Mathlib's epi/surjective and homology naturality lemmas are already used. The
   identical private surjectivity helpers in ModuleCohomologyCupProduct are not
   accessible public declarations and importing that heavy module would restore
   the collision; no available shorter public comparison replaces this proof.

4. Route and pruning: PASS. Read the entire transport and comparison proofs.
   The factor classes lift by surjectivity; Leibniz constructs their paired
   cycle; beta compares the Cech product and alpha compares the resolution
   product; injectivity of the target iso and the given cup characterization
   finish. The two refinement squares yield exactly the stated pullback classes.
   All three removed old direct proof dependencies are now explicitly listed
   above, and the source-closure pruning list is qualified as local to this item.
   sk-prop-av-cube has realized.statement = [] and realized.steps = [[]]; no
   realized unit step is bypassed or changed. No new decomposition is counted
   as progress and the restoration is not reported as two fresh hole closures.

5. DAG: PASS. Both lean.statement fields equal the delivered signatures after
   whitespace normalization. For each node proof_deps is exactly the union of
   its proof steps' uses; checked every recorded declaration against its source.
   The comparison-existence and signed-axis nodes replace the old representatives
   node in the pairing route, and the lightweight cochain core replaces the full
   Cech-product/bidegree proof imports in the helper route. Source, chapter, unit,
   blueprint, searches and creation metadata are present on both restored nodes.

Second-reader changes: completed this five-point review, made the old direct
proof-dependency pruning list explicit, and added scratch probes under a lean/
root with the sandbox .lbuild overlay. A scratch file outside a lean/ root loads
shared baseline artifacts, so its batch-probe result does not test this repair;
the corrected checks above do. No Lean proof, signature, definition or DAG route
needed repair.
