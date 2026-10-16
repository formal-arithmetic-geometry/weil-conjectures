## What changed

Repaired every duplicate named in the maintainer's return. The sole original theorem,
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_gluing`, keeps
its complete signature, universes, section parameters and visibility byte-for-byte.

The following duplicate private declarations are deleted; their existing declarations
are imported and used instead:

| Removed helper | Existing declaration and module |
| --- | --- |
| `constructible_of_restrictions` | `AlgebraicGeometry.ProEtale.constructible_of_restrictions`, `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero` |
| `counit_factor_iso` | `CategoryTheory.Adjunction.exists_iso_counit_app`, `WeilConjectures.ConstructibleSheaf.Devissage` |
| `moduleCounitOfAbelian` | Same name, `Sheaf.Paper.CondensedOpenClosedRecollement` |
| `moduleUnitOfAbelian` | Same name, `Sheaf.Paper.CondensedOpenClosedRecollement` |
| `openRestrictionPushforwardZero` | Same name, `Sheaf.Paper.CondensedOpenClosedRecollement` |
| `openUnitIsIso` | Same name, `Sheaf.Paper.CondensedOpenClosedRecollement` |
| `Topology.Stratification.exists_chain_opens_local` | `Topology.Stratification.exists_chain_opens`, `WeilConjectures.ConstructibleSheaf.Devissage` |
| `Topology.Stratification.exists_lt_diff_subset_stratum_local` | Its caller now uses the existing `exists_chain_opens`, whose proof uses the existing `exists_lt_diff_subset_stratum` in that module. |

Also removed the duplicate constructions `cokernel_subobject_iso` and `constructible_zero`.
Their callers now use `Subobject.cokernelOfLEMkIso` from the same devissage module and
`ProEtale.constructible_of_isZero` from the extension-by-zero module.
The two modules containing private helpers are brought into this proof with `import all`;
all added imports are proof-only. No existing imported module needs adaptation.

The finite-filtration argument remains complete: construct increasing open-extension
subobjects; construct integral models for the successive supported quotients by pulling
supplied stratum models to reduced closed differences; apply triangulated closure of the
integral essential image; take H0 using exact scalar extension. The scheme factoring through
a stratum is actually reduced, so no unjustified factorization of a nonreduced scheme is used.

Importing the existing devissage module introduces unrelated categorical smallness instances.
A proved private `essentiallySmallSelfInstance` specializes Mathlib's canonical
`essentiallySmallSelf.{0}` to the universes used here. Explicit mono/epi-of-isomorphism
applications avoid searching irrelevant monomorphism and epimorphism instances. No compiler
limit, definition, public instance or existing statement was changed.
The existing DAG node's proof and proof origin now name the reused declarations.
The scope-command record is `coord/changes/C1-continuous-integral-gluing-proof-scopes.md`.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.continuousConstructible_integral_gluing`
(node `lem-weil-pbc-continuous-constructible-integral-gluing`).

Holes added: none. Holes remaining in the delivered module: none. Split-off obligations: none.
This closes one local hole; the existing triangulated integral-image input still depends
on upstream holes, so this is not a claim that the theorem's transitive axioms are complete.
The empty scheme, zero strata, zero modules and equal successive opens are covered by the
same finite-filtration proof.

The repaired full module compiled without errors or warnings; the final import-pruning
check compiled in 26.8 seconds. Axiom inspection compiled in 24.4 seconds and confirmed
that the reused adjunction, topological chain, constructibility and four module support
helpers use only `propext`, `Classical.choice`, `Quot.sound`. The final theorem additionally
reports the pre-existing upstream `sorryAx`. The exact `import_prune_check.py` check that
rejected the return now passes (exit 0), including its duplicate-statement checks. Its original public theorem
signature was compared byte-for-byte with the repository and is identical. Every Lean line
has at most 100 characters. Required delivery preflight and axiom probing are run by the dry run.

## No longer needed

The eight private duplicate proofs listed above, and the duplicate constructions
`cokernel_subobject_iso` and `constructible_zero`, are no longer needed in this module.

Removed original planned proof imports:
`Sheaf.AlgebraicGeometry.LocallyClosedStratification` and
`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
The node no longer needs `lem-weil-pbc-proetale-ringed-open-closed`.
Its ringed localization-sequence and filtered-colimit comparison route is unnecessary:
closed support and the coefficient pullback comparison give the required rational model.

Removed the returned delivery's direct import of
`WeilConjectures.Topology.StratificationDense`; its existing filtration lemmas are now
accessed through `WeilConjectures.ConstructibleSheaf.Devissage`.
Removed redundant direct proof imports after a successful compile without them:
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`,
`WeilConjectures.ConstructibleSheaf.OpenClosed`,
`Sheaf.Paper.ProfinitePointPullback`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.
Also removed the redundant direct import
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle` after a successful compile.
Their required declarations remain available through retained imports.

The following list is the complete difference of project-module import closures between
the original repository module and this repaired proof, computed from the current sources.
It records pruning of this item's route, not a claim that every module leaves the targets'
global closure. The new devissage and recollement imports also bring existing dependency
closures; no statement in those closures has been copied or newly split here.

```text
Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteGlobalPresentationInternalHomColimit
Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteFinitePresentationInternalHomColimit
Sheaf.Algebra.Homology.KFlatCoefficientUniverse
Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization
Sheaf.AlgebraicGeometry.EtaleInverseImageComparisonAddition
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleActionLaws
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleConstruction
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleMapLinearity
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleObject
Sheaf.AlgebraicGeometry.EtaleInverseImageModuleUnitLinearLift
Sheaf.AlgebraicGeometry.EtaleInverseImageRingComparisonOperations
Sheaf.AlgebraicGeometry.EtaleInverseImageScalarAssociativity
Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivity
Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityLeft
Sheaf.AlgebraicGeometry.EtaleInverseImageScalarDistributivityRight
Sheaf.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
Sheaf.AlgebraicGeometry.ProEtaleClosedAbelianFilteredColimits
Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
Sheaf.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit
Sheaf.AlgebraicGeometry.ProEtaleOperations
Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
Sheaf.AlgebraicGeometry.ProEtaleRingedFilteredColimits
Sheaf.AlgebraicGeometry.ProEtaleRingedLocalizationSequence
Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
Sheaf.AlgebraicGeometry.ProEtaleSpecializationAffineCoordinates
Sheaf.AlgebraicGeometry.ProEtaleSpecializationCounit
Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections
Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison
Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
Sheaf.AlgebraicGeometry.ProductComparisonDistributivity
Sheaf.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
Sheaf.AlgebraicGeometry.Sites.WContractibleCoverSection
Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
Sheaf.CategoryTheory.CartesianScalarDistributivityTransport
Sheaf.CategoryTheory.InverseMateEquivalence
Sheaf.CategoryTheory.ModuleInverseImageAction
Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations
Sheaf.CategoryTheory.ModuleInverseImageAdjunction
Sheaf.CategoryTheory.ModuleInverseImageUnitComparison
Sheaf.CategoryTheory.SheafPullbackForgetComparison
Sheaf.CategoryTheory.SheafPullbackUnitPresentation
Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer
Sheaf.CategoryTheory.Sites.LowerShriekCorepresentability
Sheaf.CategoryTheory.Sites.LowerShriekCoveringGenerators
Sheaf.CategoryTheory.TransportScalarActionDiagrams
Sheaf.RingTheory.BoundedWContractibleExtension
Sheaf.RingTheory.ColimitFinitelyPresentedAlgebras
Sheaf.RingTheory.EtaleContraction
Sheaf.RingTheory.EtaleContractionProperties
Sheaf.RingTheory.EtaleContractionSize
Sheaf.RingTheory.FactorsThroughLocalization
Sheaf.RingTheory.FilteredColimitOfFactorization
Sheaf.RingTheory.IndEtaleStability
Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso
Sheaf.RingTheory.PrincipalWLocalization
Sheaf.RingTheory.PrincipalWLocalizationEvaluation
Sheaf.RingTheory.PrincipalWLocalizationPoints
Sheaf.RingTheory.PrincipalWLocalizationPrimeCharts
Sheaf.RingTheory.PrincipalWLocalizationSize
Sheaf.RingTheory.ProfiniteComponentRingPullback
Sheaf.RingTheory.RetainedLocalization
Sheaf.RingTheory.RetainedLocalizationProperties
Sheaf.RingTheory.RetainedLocalizationSize
Sheaf.RingTheory.StrictWCover
Sheaf.RingTheory.StrictWCoverProperties
Sheaf.RingTheory.StrictWCoverSize
Sheaf.RingTheory.WContractibleClosedLocalization
Sheaf.RingTheory.WContractibleGeometricCriterion
Sheaf.Topology.BoundedExtremallyDisconnectedCover
WeilConjectures.AlgebraicGeometry.ProEtale.Replete
WeilConjectures.AlgebraicGeometry.ProEtale.SequentialLimit
WeilConjectures.AlgebraicGeometry.ProEtale.SigmaCover
WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
WeilConjectures.RingTheory.Spectrum.Prime.Colimit
```

## Where the brief, the DAG or earlier work was wrong

The returned delivery incorrectly copied the eight already-stated results instead of
reusing them. The earlier report's assertion that the private support lemmas could not
be reused was wrong: Lean's existing `import all` mechanism makes them available without
changing their visibility or modifying the owning modules. Likewise the devissage import
can be used after supplying the canonical smallness instance explicitly and using explicit
mono/epi-of-isomorphism lemmas. The previously appended second reading described the
returned version; it has been removed so the independent reader can review this repair.

The original DAG plan used ringed `SheafOfModules` localization and filtered colimits;
the unchanged statement is about internal `Mod` objects. The implemented argument instead
uses the existing ordinary module support proofs and abelian closed support. The node's
route records these inputs and the existing module that owns the reused private helpers.
The blueprint unit's own statement and realized steps are unchanged and are not bypassed.
No new node, theorem with `sorry`, public signature or forced adaptation was introduced.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes.** Compared the delivered module with the shared
repository version. The existing theorem signature is byte-for-byte unchanged; all added
declarations are private proved helpers or a private canonical instance. The only public
import remains `Sheaf.Paper.ContinuousIntegralCoefficients`; added imports are proof-only.
Verdict: pass.

2. **Proof validity and axioms.** Compiled the module with `lcompile.py`; it exits cleanly
with no warnings, `sorry`, forbidden declarations, or hollow definitions. The existing
theorem is fully proved, and the axiom probe reports only the permitted foundational axioms
plus the pre-existing upstream `sorryAx` in its transitive dependencies. Verdict: pass.

3. **Split statements and reuse.** No statements were split off and no new DAG node was
added. Searches found no existing duplicate of the main theorem; the proof reuses the
existing constructibility, support, adjunction, filtration, and cokernel declarations
listed in the report. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing finite-open-chain and
support infrastructure, removes the obsolete ringed-localization route and redundant
imports, and records the resulting closure differences under `## No longer needed`.
Verdict: pass.

5. **DAG agreement and unit route.** The node's `proof`, `proof_deps`, and `proof_origin`
describe the declarations actually used. The unit statement and all realized filtration
steps remain unchanged; no unit is bypassed. Verdict: pass.

Changed after reading: appended this review only; no Lean proof or node content required
repair.

## Second reading by C1

1. **Signatures and accidental changes.** I compared the delivered module with the
repository version. The public theorem `continuousConstructible_integral_gluing` has the
same declaration signature, binders, universes and visibility byte-for-byte. The changes
are proof imports, private proof helpers and the proof itself; no target statement or
existing public declaration was weakened. Verdict: pass.

2. **Proof validity and axioms.** I compiled the module and all sandbox modules with
`lcompile.py`; both completed without errors or warnings. The source contains no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, `implemented_by` or hollow definition. The axiom
probe records only the permitted foundational axioms together with pre-existing upstream
`sorryAx` dependencies. Verdict: pass.

3. **Split statements and reuse.** No split-off theorem or new node was added. I searched
the library and Mathlib for the target and for the private helper names; the proof reuses
the existing declarations named in the report and does not duplicate a public theorem.
The existing node's statement is unchanged and every proof dependency is represented in
the node. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing finite filtration,
constructibility, recollement, support, and integral-image results, then removes the
obsolete ringed-localization route and redundant proof imports. The complete import
closure difference is recorded under `## No longer needed`; the unit's filtration route
is retained. Verdict: pass.

5. **DAG agreement and unit route.** I checked the node's `proof`, `proof_deps`, and
`proof_origin` against the declarations actually used in the Lean proof. The unit record
and its realized statement and steps remain intact, and no unit is bypassed. Verdict:
pass.

Changed after this reading: added this required independent review section only; no Lean
proof, statement, definition, or DAG node content required repair.
