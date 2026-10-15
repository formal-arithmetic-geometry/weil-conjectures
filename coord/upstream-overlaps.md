# Upstream overlaps after base 7d675a26

Written by L (Lean refresh 7d675a26, X-ref). Our declarations: every constant of the compiled `lean/Sheaf` oleans (no constructors or recursors) whose name is declared in its source file (3014 names). Upstream: the owners of `local/sorry_map_slopmaster2_7d675a26.jsonl.gz`. A row is a name whose last component (a) is shared with at most 4 upstream declarations, with at most 2 of ours, and has at least 6 characters, or (b) is shared with a declaration new in 7d675a26 (not in the 71d63dcf map). Two names are identical: `IsStrictlyHenselianLocalRing` and the auto-generated `HomologicalComplex.cycles.congr_simp` (not a declaration of ours). Judged by reading both statements.

| our node | our declaration (module) | upstream declaration | same notion | why |
|---|---|---|---|---|
| def-weil-pbc-henselian-terminology | `IsStrictlyHenselianLocalRing` (Sheaf.RingTheory.HenselianTerminology) | `IsStrictlyHenselianLocalRing` | **same** | ours `def … [IsLocalRing A] : Prop := HenselianLocalRing A ∧ IsSepClosed (ResidueField A)`; upstream `class … extends HenselianLocalRing R` with `isSepClosed_residueField` (new in 7d675a26, ported from proetale; `isStrictlyHenselianLocalRing_iff_henselianLocalRing_and_isSepClosed`). Our module removed, 19 importers import `WeilConjectures.Mathlib.RingTheory.Henselian` (land set 20261011T163136-L-2925583); the node record is now the upstream class |
| lem-weil-pbc-completion-of-dvr-is-dvr | `AdicCompletion.isDiscreteValuationRing` (Sheaf.RingTheory.CompletionOfDVR) | `IsRegularLocalRing.isDiscreteValuationRing` | no | ours: the adic completion of a DVR is a DVR; upstream: a regular local ring of dimension one is a DVR |
| def-weil-pbc-formal-glueing-data | `FormalGlueing.compHom` (Sheaf.RingTheory.FormalGlueingData) | `AlgebraicGeometry.Scheme.Hom.Nbhd.compHom` | no | composition of morphisms of formal glueing data vs of neighbourhoods of a scheme morphism |
| def-weil-pbc-g-ring | `RingHom.IsRegular` (Sheaf.RingTheory.GRing) | `AlgebraicGeometry.IsRegular` | no | regular ring map (G-ring fibres) vs regular scheme |
| def-exc-etale-algebra-lift | `Algebra.SquareJacobianPresentation.CoefficientLift.reduction` (Sheaf.RingTheory.JacobianPresentationLift) | `Algebra.ClosedLift.reduction` | no | reduction of a coefficient lift of a Jacobian presentation vs the reduction map of a closed lift |
| lem-weil-pbc-adic-completion-noetherian | `AdicCompletion.isNoetherianRing` (Sheaf.RingTheory.AdicCompletionNoetherian) | `GradedAlgebra.IsStandard.isNoetherianRing` | no | adic completion of a Noetherian ring vs a standard graded algebra |
| def-weil-pbc-universal-first-order-thickening | `AlgebraicGeometry.IsUniversalFirstOrderThickening.unique` (Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening) | `AlgebraicGeometry.Scheme.Modules.LocalDerivation.IsGlueValue.unique`, `AlgebraicGeometry.Scheme.Modules.IsGlueValue.unique`, `AlgebraicGeometry.IsDescentValue.unique`, `AlgebraicGeometry.IsWeilFactorization.unique` | no | uniqueness lemmas of unrelated universal properties |
| def-weil-pbc-quasi-coherent-algebra | `AlgebraicGeometry.Scheme.CommAlgebraSheaf.IsFinite` (Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra) | `CochainComplex.SubcomplexFamily.IsFinite` | no | finite quasi-coherent algebra vs finite family of subcomplexes |
| def-weil-pbc-constructible-torsion | `AlgebraicGeometry.CurveCoefficientPair.IsConstructible` (Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf) | `AlgebraicGeometry.ProEtale.IsConstructible` | no | constructibility of a coefficient pair on a curve over an algebraically closed field (étale) vs constructible sheaf of Λ-modules on the pro-étale site |
| lem-sc-global-sections-left-exact | `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor` (Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact) | `AlgebraicGeometry.ProEtale.globalSectionsFunctor` | no | Γ on 𝒪_X-modules (to AddCommGrpCat) vs Γ on pro-étale sheaves |
| def-weil-pbc-coherent-thickening-system | `AlgebraicGeometry.CoherentThickeningSystem.evaluation` (Sheaf.AlgebraicGeometry.CoherentThickeningSystem) | `CategoryTheory.Functor.Monoidal.evaluation`, `CategoryTheory.Mod.evaluation` | no | evaluation of a thickening system at n vs evaluation functors of monoidal functors / modules |
| def-weil-pbc-coherent-thickening-system | `AlgebraicGeometry.CoherentThickeningSystem.category` (Sheaf.AlgebraicGeometry.CoherentThickeningSystem) | `AlgebraicGeometry.CompactSupportFormalism.category`, `AlgebraicGeometry.Compactification.category` | no | category instance on a different structure |
| def-pc-perfect-complex | `AlgebraicGeometry.Scheme.IsPerfect` (Sheaf.AlgebraicGeometry.PerfectComplex) | `DerivedCategory.IsPerfect`, `FrobeniusModule.TraceCup.IsPerfect` | no | perfect complex on a scheme (local condition on D(𝒪_X)) vs perfect complex over a ring D(R) and a trace-cup notion |
| def-weil-pbc-etale-residue-triples | `AlgebraicGeometry.Scheme.EtaleResidueTriple.factorization` (Sheaf.AlgebraicGeometry.EtaleResidueTriples) | `AlgebraicGeometry.IsWeilFactorization.factorization` | no | field of an étale residue triple vs a Weil factorization |
| lem-galois-fpqc-morphisms-descend | `AlgebraicGeometry.Scheme.baseChangeMap` (Sheaf.AlgebraicGeometry.FpqcMorphismsDescend) | `AlgebraicGeometry.ProEtale.baseChangeMap`, `AlgebraicGeometry.Etale.baseChangeMap`, `AlgebraicGeometry.baseChangeMap` | no | ours: `pullback pU f ⟶ pullback pW f` from α : U ⟶ W over S; upstream `AlgebraicGeometry.baseChangeMap`: `pullback f T'.hom ⟶ pullback f T.hom` along φ in Over S: same map with the factors in the other order, not the same declaration; the Etale/ProEtale ones are base-change maps of sheaves |
| lem-weil-pbc-truncation-couple-morphism | `CategoryTheory.TruncationExchange.inclusion` (Sheaf.AlgebraicGeometry.TruncationExchangeCouple) | `AlgebraicGeometry.Scheme.FiniteEtale.FiniteSubfield.inclusion` | no | different structures |
| def-weil-pbc-ample-invertible-module | `AlgebraicGeometry.Scheme.Modules.IsAmple` (Sheaf.AlgebraicGeometry.Ample) | `AlgebraicGeometry.IsAmple` | no | ours: ample invertible 𝒪_X-module on any scheme; upstream `IsAmple f M` asks a very ample power with a closed immersion into projective space over K (its docstring: not ample on a non-proper K-scheme) |
| def-pc-field-tower | `FieldExtension.degree` (Sheaf.FieldTheory.FieldTower) | `AlgebraicGeometry.Scheme.Hom.degree`, `AlgebraicGeometry.Scheme.Divisor.degree`, `AlgebraicGeometry.Scheme.Modules.degree` | no | degree of a field extension vs degree of a scheme morphism / divisor / module |
| lem-weil-pbc-constructible-is-retrocompact | `Topology.IsConstructible.isRetrocompact` (Sheaf.Topology.ConstructibleIsRetrocompact) | `TopologicalSpace.NoetherianSpace.isRetrocompact` | no | ours: a constructible set is retrocompact (any space); upstream: every set of a Noetherian space is retrocompact |
| def-sc-sheaf-cohomology-functor, def-sc-ringed-space-module-cohomology | `AlgebraicGeometry.RingedSpace.globalSectionsFunctor` (Sheaf.Topology.RingedSpaceModuleCohomology) | `AlgebraicGeometry.ProEtale.globalSectionsFunctor` | no | Γ on modules over a ringed space vs Γ on pro-étale sheaves |
| def-weil-pbc-module-stalk | `PresheafOfModules.stalkObj` (Sheaf.Topology.PresheafModuleStalkFunctor) | `AlgebraicGeometry.WeilSheaf.stalkObj` | no | stalk of a presheaf of modules vs stalk of a Weil sheaf |
| def-weil-pbc-module-stalk | `PresheafOfModules.stalkMap` (Sheaf.Topology.PresheafModuleStalkFunctor) | `AlgebraicGeometry.WeilSheaf.stalkMap` | no | as above |
| def-sp-filtration | `CategoryTheory.DecreasingFiltration.IsFinite` (Sheaf.CategoryTheory.Filtration) | `CochainComplex.SubcomplexFamily.IsFinite` | no | finite filtration vs finite family of subcomplexes |
| lem-galois-aut-profinite | `CategoryTheory.SetFunctorAut.evaluation` (Sheaf.CategoryTheory.Galois.AutProfinite) | `CategoryTheory.Functor.Monoidal.evaluation`, `CategoryTheory.Mod.evaluation` | no | different structures |
| def-sp-exact-couple | `CategoryTheory.BigradedExactCouple.d_comp_d` (Sheaf.CategoryTheory.ExactCouple) | `CochainComplex.InternalHom.d_comp_d` | no | d² = 0 of an exact couple vs of the internal Hom complex |
| def-sp-truncation-couple | `CategoryTheory.TruncationCouple.transition` (Sheaf.CategoryTheory.TruncationCouple) | `AlgebraicGeometry.Scheme.Torsor.transition` | no | different structures |
| def-sp-truncation-couple | `CategoryTheory.TruncationCouple.triangle` (Sheaf.CategoryTheory.TruncationCouple) | `CategoryTheory.DerivedMonoidal.triangle`, `CategoryTheory.NatTrans.Triangle.triangle`, `HomotopyCategory.MonoidalCategory.triangle` | no | different structures |
| def-pod-internal-module | `CategoryTheory.InternalModule.category` (Sheaf.CategoryTheory.InternalModule) | `AlgebraicGeometry.CompactSupportFormalism.category`, `AlgebraicGeometry.Compactification.category` | no | different structures |
| def-sp-convergence | `CategoryTheory.BigradedExactCouple.pageInfinity` (Sheaf.CategoryTheory.ExactCoupleConvergence) | `CategoryTheory.SpectralSequence.pageInfinity` | no | E_∞ of a bigraded exact couple vs of upstream `SpectralSequence`; different encodings of spectral sequences (no bridge upstream) |
| def-sp-convergence | `CategoryTheory.BigradedExactCouple.IsRegular` (Sheaf.CategoryTheory.ExactCoupleConvergence) | `AlgebraicGeometry.IsRegular` | no | regular exact couple vs regular scheme |
| def-sp-convergence | `CategoryTheory.BigradedExactCouple.AbutsTo` (Sheaf.CategoryTheory.ExactCoupleConvergence) | `CategoryTheory.SpectralSequence.AbutsTo` | no | convergence of an exact couple vs of a `SpectralSequence`: analogous notion, different encoding |
| def-sp-convergence | `CategoryTheory.BigradedExactCouple.imageFiltration` (Sheaf.CategoryTheory.ExactCoupleConvergence) | `CategoryTheory.Abelian.SpectralObject.imageFiltration` | no | analogous notion on `SpectralObject`, different encoding |
| lem-pqf-leray-five-term | `CategoryTheory.BigradedExactCouple.bottomEdge` (Sheaf.CategoryTheory.LerayFiveTerm) | `CategoryTheory.Abelian.SpectralObject.bottomEdge` | no | edge map of an exact couple vs of a `SpectralObject`; different encoding |
| lem-pqf-leray-five-term | `CategoryTheory.BigradedExactCouple.leftEdge` (Sheaf.CategoryTheory.LerayFiveTerm) | `CategoryTheory.Abelian.SpectralObject.leftEdge` | no | as above |
| def-pc-ring-tensor-cohomology | `RingTensorCohomology.baseChangeMap` (Sheaf.Algebra.Homology.RingTensorCohomology) | `AlgebraicGeometry.ProEtale.baseChangeMap`, `AlgebraicGeometry.Etale.baseChangeMap`, `AlgebraicGeometry.baseChangeMap` | no | base change on ring-tensor cohomology vs on pullbacks / étale sheaves |
| def-weil-derived-tensor | `AlgebraicGeometry.Scheme.derivedTensor` (Sheaf.Algebra.Homology.DerivedTensor) | `AlgebraicGeometry.Etale.derivedTensor`, `AlgebraicGeometry.ProEtale.derivedTensor` | no | derived tensor of complexes of 𝒪_X-modules (K-flat replacement) vs on D(X_ét, A) / pro-étale |
| def-weil-pbc-formal-glueing-data | `FormalGlueing.Hom` (Sheaf.RingTheory.FormalGlueingData) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| def-weil-pbc-formal-glueing-data | `FormalGlueing.restrict` (Sheaf.RingTheory.FormalGlueingData) | `AlgebraicGeometry.Etale.NormalizedTower.restrict`, `CategoryTheory.Limits.RelativeLimitPresentation.restrict`, `WLocalization.Stratification.Index.restrict` | no | generic component (structure field / instance) of a different structure |
| lem-weil-pbc-smooth-product-algebra | `Algebra.Smooth.prod` (Sheaf.RingTheory.SmoothProductAlgebra) | `PrespectralSpace.prod`, `Algebra.FormallyUnramified.prod`, `Algebra.IndZariski.prod`, `RingHom.BijectiveOnStalks.prod` … | no | smoothness of a finite product of algebras; upstream has `FormallySmooth.prod`, `Etale.prod`, `FinitePresentation.prod` (ingredients, not the statement) |
| def-weil-pbc-module-cohomology-fmap | `AlgebraicGeometry.Scheme.Modules.ModuleCohomologyFMapData.map` (Sheaf.AlgebraicGeometry.ModuleCohomologyFMap) | `CategoryTheory.Rationalization.map`, `AlgebraicGeometry.Etale.NormalizedTower.map`, `CategoryTheory.FiniteFamilies.map`, `WContractification.RestrictClopen.map` … | no | generic component (structure field / instance) of a different structure |
| def-weil-pbc-coherent-thickening-system | `AlgebraicGeometry.CoherentThickeningSystem.Hom` (Sheaf.AlgebraicGeometry.CoherentThickeningSystem) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| lem-weil-pbc-first-order-thickening-base-change | `AlgebraicGeometry.IsFirstOrderThickening.baseChange` (Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange) | `AlgebraicGeometry.Compactification.Refinement.baseChange`, `AlgebraicGeometry.CompactSupportFormalism.baseChange` | no | generic component (structure field / instance) of a different structure |
| lem-galois-fpqc-singleton-fully-faithful-0241 | `CategoryTheory.Over.DescentDataCategory.Hom` (Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| lem-weil-pbc-truncation-couple-morphism | `CategoryTheory.TruncationExchange.f` (Sheaf.AlgebraicGeometry.TruncationExchangeCouple) | `CategoryTheory.PreZeroHypercover.RelativeLimitPresentation.f`, `CategoryTheory.PreOneHypercover.RelativeLimitPresentation.f` | no | generic component (structure field / instance) of a different structure |
| lem-pod-lisse-module-sheaves-as-module-objects | `AlgebraicGeometry.Scheme.LambdaModuleObject.Hom` (Sheaf.Paper.LisseModuleSheaves) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| def-pod-finite-continuous-module | `CategoryTheory.FiniteContinuousModule.forget` (Sheaf.CategoryTheory.FiniteContinuousModule) | `CategoryTheory.ShortComplex.forget`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.forget` | no | generic component (structure field / instance) of a different structure |
| def-sp-filtration | `CategoryTheory.FilteredObject.Hom` (Sheaf.CategoryTheory.Filtration) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| def-sp-exact-couple | `CategoryTheory.BigradedExactCouple.d` (Sheaf.CategoryTheory.ExactCouple) | `ChainComplex.ResolutionOfLiftsAlongEpi.Stage.d` | no | generic component (structure field / instance) of a different structure |
| def-weil-pbc-delta-functor | `CategoryTheory.CohomologicalDeltaFunctor.Hom` (Sheaf.CategoryTheory.DeltaFunctor) | `Algebra.ClosedLift.Index.Hom`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.Hom`, `CategoryTheory.Limits.RelativeLimitPresentation.Hom`, `AlgebraicGeometry.Compactification.Triangle.Hom` … | no | generic component (structure field / instance) of a different structure |
| def-sp-truncation-couple | `CategoryTheory.TruncationCouple.f` (Sheaf.CategoryTheory.TruncationCouple) | `CategoryTheory.PreZeroHypercover.RelativeLimitPresentation.f`, `CategoryTheory.PreOneHypercover.RelativeLimitPresentation.f` | no | generic component (structure field / instance) of a different structure |
| def-pod-internal-module | `CategoryTheory.InternalModule.forget` (Sheaf.CategoryTheory.InternalModule) | `CategoryTheory.ShortComplex.forget`, `AlgebraicGeometry.ProEtale.StrictWeilComplex.forget` | no | generic component (structure field / instance) of a different structure |
| def-pc-ring-tensor-cohomology | `RingTensorCohomology.restrict` (Sheaf.Algebra.Homology.RingTensorCohomology) | `AlgebraicGeometry.Etale.NormalizedTower.restrict`, `CategoryTheory.Limits.RelativeLimitPresentation.restrict`, `WLocalization.Stratification.Index.restrict` | no | generic component (structure field / instance) of a different structure |

52 rows, 1 same notion, 0 unsure.

## Nodes whose upstream tagged declaration changed state in 7d675a26

| node | our record | upstream | same notion | note |
|---|---|---|---|---|
| lem-sc-ext-locally-free | `AlgebraicGeometry.Scheme.Modules.locallyFreeExtAddEquivH` (def, Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology) | `AlgebraicGeometry.Scheme.Modules.nonempty_ext_addEquiv_H` (WeilConjectures.AlgebraicGeometry.Modules.Ext:252, now sorry-free) | no | ours chooses the equivalence `Ext F G i ≃+ (Fᵛ ⊗ G).H i` (data); upstream states only `Nonempty`; the node is closed on slopmaster2 by the upstream theorem, our record stays (data a citer may use) |



## Sync to ffb7b906069b754b60fc5d090a85e9ae4209561e (2026-10-13)

The new upstream declarations were compared with the source of our modules, including full-name
matches and alternate encodings. The canonical upstream definitions replace ours. Imports in
all users are redirected; projectivity now uses upstream's finite coordinate type, varieties
and smooth projective curves use the upstream classes, and the change-of-field proof transports
`Scheme.dim` through its proved equality with topological Krull dimension.

| retired module | canonical upstream module | reason |
|---|---|---|
| `Sheaf.AlgebraicGeometry.EtaleSheaves` | `WeilConjectures.AlgebraicGeometry.EtaleSheaves` | Same five notions, including torsion Ab cohomology; upstream ported our definitions. |
| `Sheaf.AlgebraicGeometry.Morphisms.Projective` | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` | Same H-projectivity and projectivity; upstream accepts any finite coordinate type. |
| `Sheaf.AlgebraicGeometry.Variety` | `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective` | Same variety and integral curve; local-ring dimension equals topological dimension. |
| `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve` | `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective` | Same smooth projective integral curve. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | `WeilConjectures.AlgebraicGeometry.Curve.Estimate` | Same Kummer cohomology calculation, proved upstream. |
| `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerExtension` | `WeilConjectures.AlgebraicGeometry.Modules.QcqsSections` | Same extension after multiplying by a power, proved upstream. |
| `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion` | `WeilConjectures.AlgebraicGeometry.Modules.QcqsSections` | Same power-torsion criterion, proved upstream. |
| `Sheaf.AlgebraicGeometry.NormalizationProperties` | `WeilConjectures.AlgebraicGeometry.Regular` | Canonical normalization properties proved upstream; the old extra birational-conjunction wrapper had no users. |
| `Sheaf.AlgebraicGeometry.LowerStarPlusTransitionComp` | `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.TransitionComposition` | Same composition theorem; upstream explicitly takes the composite arrow and witnesses. |
| `Sheaf.CategoryTheory.ImageFiltration` | `WeilConjectures.CategoryTheory.Abelian.Filtration` | Same image filtration; seven users redirected. |

The extension modules `Sheaf.AlgebraicGeometry.Dimension`, `GlobalSectionsLeftExact`, and
`Sheaf.CategoryTheory.Filtration` retain their additional API but use upstream's relative
dimension, global-sections functor, and decreasing-filtration structure. Filtration's quotient
and graded piece now reuse upstream image and graded piece. The bigraded shifted-map exact
couple now wraps the canonical upstream ExactCouple in a single `toExactCouple` field; shifted
accessors and constructors provide the existing API. Its independent mathematical data
structure is retired in place, and the extension module retains only pages and derived APIs.
Private helper proofs have different signatures from the corresponding new public lemmas.
They are renamed `isFinitePresentation_free_sheaf` and `transport_left_congr_sheaf` so their
visible aliases coexist with the new upstream API; they introduce no mathematical data.

The removed injective-preservation declaration is renamed to
`preservesInjectiveObjects_lowerStar_of_abelian` in its node and audit records. Two WeilSheaf
base-change pointers now name `WeilComplex.nonempty_upperStar_derivedLowerShriek_iso`.
`lem-sc-field-brauer-comparison` has its stale Lean record cleared: upstream replaced the use of
that general comparison by direct Cech cohomology for C1 fields, which does not establish the
general equivalence. Its removed record and reason are retained as `lean_removed`.

The private duplicate internal-Hom comparison proof in
`Sheaf.ConstructibleSheaf.EtalePullbackInternalHom` is removed; its thin existential-isomorphism
wrapper now uses upstream `Etale.isIso_ihomComparison_upperStar`. The smooth projective curve
connectedness wrapper follows upstream instances, removing its redundant sorry.

The strict-henselization adapters also retire
`Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal` in favor of
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization`, and
`Sheaf.Paper.StrictHenselizationLocalStructure` in favor of
`WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal`. The four node records
`def-weil-pbc-strict-henselization-limit`, `lemma-weil-pbc-affine-neighbourhood-cofinal`,
`lem-weil-pbc-strict-henselization-local-structure`, and
`def-weil-pbc-strict-henselization-structural-map` now name the canonical upstream ring,
initial inclusion, local-structure instances, and structure map. Our smaller-index diagrams
retain only their presentation and transport API.

This sync retires twelve modules in total. Twelve local Lean records are repointed or cleared
in the broad API migration, three filtration/exact-couple records and four strict-henselization
records are updated, and the two earlier Weil-complex repoints are replayed. The queue delta
and upstream sorry census are generated from the final verified build by the sync routine.

The exact canonical Projective section is extracted from Curve.SmoothProjective into
WeilConjectures.AlgebraicGeometry.Morphisms.Projective and publicly re-imported.
This removes the cycle from Chow relative ampleness back to finite-free direct-image
cohomology; every projectivity notion still has one definition.
