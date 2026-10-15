## What changed

Replaced the sole sorry in `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement` by a compiling proof of its unchanged statement. No existing definition, signature, public import, or module command changes. Its 18 private supporting lemmas are proved. The proof constructs the exceptional sheaf right adjoint from a kernel, proves exact closed pushforward by joint zero detection, derives all four adjunctions, constructs both natural distinguished triangles, proves their signed shift compatibility, proves left t-exactness, and supplies both functorial common-bound injective resolution models.

The triangle argument uses the proved source theorem `Pretriangulated.Recollement.existsUnique_distTriang_counit_unit`. Uniqueness proves naturality and compatibility with the signed shift functor. The source module-object category has the required Grothendieck theorem. Functorial injective embeddings come from degree-zero evaluation of the proved K-injective replacement; common-bound models use good truncation followed by the existing bounded resolution theorem.

Added `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`, with a complete proof from the closed counit. Its private helpers adapt the proved source finite-family detection argument directly to abelian groups: local injectivity of sheafification, equality at a filtered Kan-extension stage, quasi-compact covering factorization, sheaf separation, and joint detection of isomorphisms. The supported unit then follows from its two restrictions and the triangle identity. The zero open restriction of a closed direct image is proved sectionwise over empty base changes.

Added `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit`, leaving precisely the geometric closed counit as the smaller input. It has no open complement, coefficient module objects, derived category, exceptional adjoint, triangle, shift, or resolution clause. Its node and docstring give the affine-basis proof in full.

The item's proof, proof dependencies and proof origin now describe the actual route. No unit-level realized statement or proof-step node was bypassed: this recollement statement is an auxiliary below those nodes.

The original signature has named instance binders that the unused-variable linter flags once its sorry is removed. A scoped unused-variable option preserves the signature verbatim. A scoped heartbeat budget handles nested instance witnesses without changing the 60-second compilation limit.

Validation: all three delivered modules compile without warnings via `lcompile.py --all`. Independent axiom inspection found only `propext`, `Classical.choice`, `Quot.sound`, and the documented `sorryAx` dependencies. The second reading below records the remaining checks; the final delivery-tool result records delivery status.

## Proved and sorry left

Closed the hole in `AlgebraicGeometry.ProEtale.CondensedRing.condensed_open_closed_recollement` (node `lem-weil-pbc-condensed-open-closed-recollement`). No sorry remains in the item module.

Also proved `AlgebraicGeometry.ProEtale.abelian_closed_support` (new node `lem-weil-pbc-proetale-abelian-closed-support`), including its supported-unit assertion and the finite-family joint conservativity needed for it. No sorry remains in that module.

Added one hole: `AlgebraicGeometry.ProEtale.abelian_closed_counit` (new node `lem-weil-pbc-proetale-abelian-closed-counit`). The delivery closes one old hole and adds one strictly smaller hole: a decomposition, net zero locally, with a further new support theorem proved. It does not claim an axiom-free target proof.

The remaining counit proof needs the affine-open restriction comparisons for the actual adjunction, the ind-etale affine-basis equivalences, and the opposite closed-site adjunction computation of inverse image as sheafification after precomposition by the closed lift. For a closed sheaf G the resulting presheaf is naturally G because the site unit is invertible; sheafification then leaves it unchanged. These comparisons identify the actual counit, and affine-local inverses glue. The source is Stacks 09AA/09BL/09BK. The empty closed part, nonreduced thickening, and infinitely generated defining ideal introduce no exception; no quasi-compact open complement is needed for this input. During this session the larger abelian-support split was itself reduced by a complete direct proof, leaving only this counit calculation.

The main proof still uses the existing holed theorem `CochainComplex.exists_functorial_bounded_injective_resolution` (node `lem-weil-pbc-functorial-bounded-injective-resolution`). No hole was added to that module. Other imported dependencies can contain inherited sorries.

## No longer needed

Removed these direct proof imports:

- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`

The second reading also removed the redundant newly added proof import
`WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`; a scratch compile confirmed it was
unnecessary.

The old route's following proof-dependency edges are removed. Some definitions remain statement dependencies, and other target branches may still need these nodes:

- `def-weil-pbc-proetale-operations`
- `lem-pc-pre-derived-adjoint-functors-general`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-sf-triangle-morphism-iso`
- `lem-weil-pbc-complex-ses-triangle`
- `lem-weil-pbc-dplus-injective-representative`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-grothendieck-functorial-injective-embedding`
- `lem-weil-pbc-hom-into-triangle-exact`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-proetale-weakly-etale-localization`
- `prop-pur-kinjective-resolutions-exist`

Source traversal at the second reading (including `import all` edges) finds 767 non-Mathlib modules in this item's original import closure and 635 after the delivery. These 139 modules leave this item's closure, while 7 modules enter it. This is a source-level comparison with the current shared checkout, not the pinned whole-target ledger, and makes no claim that these modules leave every target's closure:

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.EtaleAbelianDirectImageInternal`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLift`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAbelianLiftOperations`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleActionLaws`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleConstruction`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleMapLinearity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleObject`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModuleUnitLinearLift`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingAdjunction`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingComparisonOperations`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageRingLift`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarAssociativity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityLeft`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityRight`
- `Sheaf.AlgebraicGeometry.EtaleRingDirectImageComparison`
- `Sheaf.AlgebraicGeometry.EtaleRingDirectImageOperations`
- `Sheaf.AlgebraicGeometry.EtaleRingInverseImageCounit`
- `Sheaf.AlgebraicGeometry.EtaleRingInverseImageUnit`
- `Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs`
- `Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation`
- `Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineContractibleExtension`
- `Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover`
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`
- `Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying`
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSiteLimits`
- `Sheaf.AlgebraicGeometry.ProEtaleQcqsSubsite`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero`
- `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProductComparisonDistributivity`
- `Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus`
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation`
- `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections`
- `Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection`
- `Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation`
- `Sheaf.CategoryTheory.CartesianScalarDistributivityTransport`
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.InverseMateEquivalence`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Sheaf.CategoryTheory.ModuleInverseImageAction`
- `Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations`
- `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.SheafAbelianObjectsBijective`
- `Sheaf.CategoryTheory.SheafAbelianObjectsInjective`
- `Sheaf.CategoryTheory.SheafAbelianObjectsSurjective`
- `Sheaf.CategoryTheory.SheafPullbackForgetComparison`
- `Sheaf.CategoryTheory.SheafPullbackUnitPresentation`
- `Sheaf.CategoryTheory.SheafRingObjectReconstruction`
- `Sheaf.CategoryTheory.SheafRingObjectsBijective`
- `Sheaf.CategoryTheory.SheafRingObjectsInjective`
- `Sheaf.CategoryTheory.SheafRingObjectsSurjective`
- `Sheaf.CategoryTheory.SheavesAbelianForward`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresAbelian`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRing`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingCore`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresRingMorphism`
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.CategoryTheory.SiteExtensionByZeroExact`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`
- `Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer`
- `Sheaf.CategoryTheory.Sites.LowerShriekCorepresentability`
- `Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators`
- `Sheaf.CategoryTheory.TransportScalarActionDiagrams`
- `Sheaf.Paper.SiteRestrictionExact`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.RingTheory.BoundedWContractibleExtension`
- `Sheaf.RingTheory.ColimitFinitelyPresentedAlgebras`
- `Sheaf.RingTheory.EtaleContraction`
- `Sheaf.RingTheory.EtaleContractionProperties`
- `Sheaf.RingTheory.EtaleContractionSize`
- `Sheaf.RingTheory.FactorsThroughLocalization`
- `Sheaf.RingTheory.FilteredColimitOfFactorization`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso`
- `Sheaf.RingTheory.PrincipalWLocalization`
- `Sheaf.RingTheory.PrincipalWLocalizationEvaluation`
- `Sheaf.RingTheory.PrincipalWLocalizationPoints`
- `Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts`
- `Sheaf.RingTheory.PrincipalWLocalizationSize`
- `Sheaf.RingTheory.ProfiniteComponentRingPullback`
- `Sheaf.RingTheory.RetainedLocalization`
- `Sheaf.RingTheory.RetainedLocalizationProperties`
- `Sheaf.RingTheory.RetainedLocalizationSize`
- `Sheaf.RingTheory.StrictWCover`
- `Sheaf.RingTheory.StrictWCoverProperties`
- `Sheaf.RingTheory.StrictWCoverSize`
- `Sheaf.RingTheory.WContractibleClosedLocalization`
- `Sheaf.RingTheory.WContractibleGeometricCriterion`
- `Sheaf.Topology.BoundedExtremallyDisconnectedCover`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Replete`
- `WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit`
- `WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover`
- `WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`
- `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`
- `WeilConjectures.CategoryTheory.Sites.WeaklyContractible`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.RingTheory.Spectrum.Prime.Colimit`

The arbitrary-ringed open/closed localization theorem and its separate comparison with monoidal module objects are no longer needed here. The general derived-adjunction colimit diagrams, general K-injective total-derived statement, prescribed-bound representative and complex-SES triangle statements are replaced by proved source APIs and explicit constructions. The planned `lem-weil-pbc-grothendieck-functorial-injective-embedding` needs no Lean attachment for this proof, because that embedding is constructed from the existing K-injective functor.

## Where the brief, the DAG or earlier work was wrong

The planned `proEtale_ringed_open_closed` statement uses `SheafOfModules` and a slice presentation, while this item uses monoidal module objects and the current finite-coefficient inverse-image API. An explicit comparison would have been required. The final proof avoids that comparison: it proves joint conservativity and supported units directly for abelian sheaves, then fully proves the monoidal-adjunction and scalar-change lifts to the module-object category.

The legacy source closed-immersion and derived-localization modules cannot simply be imported: their old `UpperLowerStar.Defs` declarations collide with current finite-coefficient definitions already in this item. Their proved detection and zero-composite arguments can be adapted directly to Ab without importing the legacy definitions, as done here. The generic triangulated recollement module has no such conflict.

The earlier searches missed the useful proved source recollement theorem and several existing derived APIs. Importing the corresponding separate Sheaf statement modules would retain avoidable holes. No existing statement is disputed or weakened, and no arbitrary data is defined from an unproved existence statement.


## New nodes

`lem-weil-pbc-proetale-abelian-closed-support`: module `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`, declaration `AlgebraicGeometry.ProEtale.abelian_closed_support`. Fully proved from the smaller closed-counit input and direct finite-family conservativity, with a complete proof in its node and docstring.

`lem-weil-pbc-proetale-abelian-closed-counit`: module `Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedCounit`, declaration `AlgebraicGeometry.ProEtale.abelian_closed_counit`. The one remaining new sorry, for the geometric counit. Sources: Stacks Tags 09AA, 09BL and 09BK. It reuses the existing ind-etale affine basis, affine closed-site functor properties and closed-site adjunction. The latter is an auxiliary site-adjunction tool; it does not replace a unit-level proper-base-change step.

Both new nodes inherit the item's chapter, unit and blueprint ancestor. Searches include LeanFinder, Loogle and Mathlib grep; LeanSearch was attempted and unavailable. Blueprint searches found no identical abelian statement. No change record is needed: existing signatures, definitions, public imports and module commands remain identical.

## Second reading by D3

1. **Interfaces — PASS.** Read all three modules and diffed the item against the shared
repository. The existing theorem signature is byte for byte identical, including every
instance binder and every conjunct. The existing public imports, visibility and module
commands are unchanged. The only added public declarations are the two recorded abelian
lemmas. No definition or target statement changes, and no forced adaptations or change
records are needed.

2. **Proof and axioms — PASS as a decomposition.** Independently compiled the three-file
set with `lcompile.py --all`: no errors or warnings. The main module and support module
have no sorry; the counit module has exactly its one named theorem with proof `by sorry`.
There are no forbidden declarations or hollow definitions. Scratch `#print axioms` checks
of all three public theorems show only `propext`, `Classical.choice`, `Quot.sound` and
`sorryAx`, which is expected from the documented remaining inputs. The source recollement
uniqueness theorem and K-injective replacement separately use only the three allowed
axioms. The exceptional adjoint is the explicit kernel functor followed by closed
restriction; its data is not an arbitrary witness from an unproved existence theorem.
The chosen connecting arrows are uniquely determined by their distinguished triangles.

3. **Split statements — PASS.** Checked the closed counit against Stacks
[09AA](https://stacks.math.columbia.edu/tag/09AA),
[09BL](https://stacks.math.columbia.edu/tag/09BL) and
[09BK](https://stacks.math.columbia.edu/tag/09BK), and the support assertion against
[09AH](https://stacks.math.columbia.edu/tag/09AH). The affine-basis argument identifies
the actual adjunction counit, not merely an unrelated object isomorphism. Empty closed
parts, the identity closed immersion, nonreduced thickenings and ideals without finite
generation are covered; the support theorem retains the quasi-compact open hypothesis.
The one new hole is strictly the geometric abelian counit, with none of the coefficient,
exceptional-adjoint, derived-triangle, shift or resolution conclusions of the item. Its
docstring gives the complete affine-basis proof and globalization. Repeated LeanFinder,
Loogle and Mathlib grep searches with different queries, plus repository searches, found
no proved exact replacement. The legacy ModuleCat counit is itself sorry and its old
inverse-image definitions conflict with the current API; the direct Ab proof route is
therefore justified. Closing that geometry requires the site-comparison work described
in the report, rather than a short missing tactic.

4. **Route and pruning — PASS after repair.** Read the proof from the final theorem
through all 18 private helpers. The module/scalar adjunction lifts, kernel right adjoint,
exactness by cokernel detection, derived full faithfulness, signed shift argument and
common-bound truncation/resolution clauses each prove the corresponding original
conclusion. The proof uses the existing proved recollement API and existing bounded
resolution statement. Checked `sk-thm-properbasechange.realized`: the item is not one of
the unit's statement or step realizers; all those realizers and the unit record remain
unchanged. Every removed old `proof_deps` edge is listed above. Removed the redundant new
proof import `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf`, verified by compiling
a scratch copy without it. Recomputed the source closure with `import all` edges and
updated the stale module-pruning list and counts; these are explicitly local source
figures, not whole-target ledger progress.

5. **DAG — PASS after repair.** The main node changes only the permitted proof fields.
Its `proof_deps` is exactly the union of its proof-step uses and agrees with the Lean
reduction. Each new node has source, complete proof steps, dependency union, search
records, status, creation provenance, blueprint ancestry, chapter/unit and verbatim Lean
statement. The support node describes the actual finite-family conservativity proof and
the counit node describes the remaining affine comparison. Corrected the support node's
stale search verdict, which incorrectly said arbitrary-ringed localization was used,
and recorded the independent replacement searches on both new nodes.

Changes made by this reading: one redundant proof import removed; stale search metadata
corrected and independent searches recorded; pruning report recalculated; this review
appended. No proof body, existing signature, definition, public import, or hole count
changed. The result is one original hole closed and one smaller hole added: net zero
locally, a decomposition rather than an axiom-free proof of the target.
