## What changed

Replaced the sole sorry in `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizingLowerStar_preservesCoproducts` with a complete Lean reduction. The theorem's signature, universes, visibility and public imports are unchanged. No existing definition or statement is repaired or changed; no consumer adaptation or change record is needed.

The proof has two ingredients. `condensed_boundedBelow_preservesCoproduct` is proved for every qcqs morphism and every condensed commutative coefficient ring, for families with a common lower cohomology bound. It uses the already formalized ordinary bounded-below qcqs continuity theorem on finite partial sums. The private universal-property lemma requires preservation only of this particular filtered diagram, rather than all diagrams of the same shape. Strictly bounded-below representatives and homology detection then give the actual derived coproduct comparison. Both comparison-factorization equalities use Mathlib’s `sigmaComparison_map_desc`.

The second ingredient, `ellAdic_proper_lowerTail_bound`, is the one remaining obligation: a single uniform upper-amplitude bound for discarded lower truncation tails on the source localizing hull. The complete Lean long-exact-sequence argument now derives the canonical lower-truncation cohomology isomorphism from this bound, killing degrees q and q+1 of the first term of the image triangle. The original module proves that truncation preserves coproducts, applies bounded-below continuity to each truncated family, and checks the natural square of canonical coproduct comparisons degree by degree. The coproduct itself remains in the hull by its defining closure property. This avoids a separate ind-constructible-heart interface and requires no assertion about the entire ambient derived category.

The unit route is retained: this is the coproduct step for the identity compactification of a proper map, used by the existing proper pushforward/right-adjoint construction. The unit `sk-cor-existence-ii` has no separately realized statement or proof-step nodes that this reduction bypasses.

Validation: all three delivery modules compile together. The unchanged immediate consumer `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` was also copied temporarily and compiled against the new modules; both calls to the assigned theorem work unchanged. Its identical temporary copy was removed from the sandbox. The uniform-bound docstring records the lower-tail argument, including eventual invertibility in both relevant cohomological degrees and the ordinary, uncompleted coefficient convention. Empty families are included in every coproduct universal-property proof.

## Proved and sorry left

Assigned baseline: one sorry, in `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizingLowerStar_preservesCoproducts`. Its proof body is now complete. This is a **decomposition**, not a net hole-closing proof: one upper hole is replaced by one strictly smaller uniform-truncation obligation, and there are zero sorries in the assigned module.

New theorem proved without a local sorry: `AlgebraicGeometry.ProEtale.CondensedRing.condensed_boundedBelow_preservesCoproduct` (node `lem-sfb-adic-proper-bounded-below-coproducts`). Both private helpers in that module, and the coproduct-support and truncation-preservation helpers in the assigned module, are proved.

Exactly one sorry remains in the delivery: `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_proper_lowerTail_bound`, in `lean/Sheaf/AlgebraicGeometry/EllAdicProperTruncationBound.lean`, node `lem-sfb-adic-proper-truncation-bound`. It needs the geometric heart bound, containment of the hull in the ind-constructible cohomology class, and extension of the upper amplitude bound through the lower-truncation tower using left completeness and Milnor. The node and docstring give the complete argument and its source. This remaining statement asserts only cohomological support of the image of a lower tail; it assumes neither a coproduct assertion, a canonical comparison isomorphism, nor the assigned theorem.

Actual counts: assigned 1 -> 0; new holes 1; total local holes 1. No axiom, hollow definition, arbitrary witness chosen in a definition, or signature change is introduced. A temporary `#print axioms` audit reports exactly `propext`, `Classical.choice`, and `Quot.sound` for `condensed_boundedBelow_preservesCoproduct`: this ingredient is fully proved, including its transitive proof dependencies. The assigned theorem also reports `sorryAx`, as expected from its one explicit remaining uniform-bound input. Temporary Lean edge-case checks also proved the lower-tail assertion for identity functors with c=0 in every degree, proved it whenever the tail is already zero, and instantiated bounded-below coproduct preservation for the empty family. The temporary audit module was removed.

## No longer needed

The five original proof imports are removed:

- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`

The new bounded-below proof also compiled after removing redundant direct imports of `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products` and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, and the redundant public import of `Mathlib.Algebra.Homology.DerivedCategory.TStructure`; the assigned module likewise needs no direct Products import, nor the redundant direct import of `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure` after formalizing the tail-triangle step. The new proof uses `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` to send that triangle to a distinguished triangle.

The main node no longer takes `det-def-localizing-closure-ctf-equals-bc`, `det-ambient-ind-derived-sums`, `sk-lem-proper-unbounded-window-ii`, `det-prop-int-compactness-direct-sums`, the fibre-dimension bound, or the four local-triviality/chart/resolution nodes as direct proof dependencies. Equality Dctf=Dbc and the finite-interval sum-induction route are unnecessary in the delivered argument. The ind-cohomology and geometric upper-bound facts remain in the mathematical proof of the new uniform-truncation node; they are not claimed to have been eliminated from all future work. In particular only the direct-sum conclusion of the former full unbounded-window sum theorem is superseded by the proved bounded-below theorem plus the truncation square.

The following complete list is the difference of non-Mathlib import closures of the assigned module before and after this delivery (349 modules). It records pruning from this module's Lean import closure, not a claim that every entry leaves the global target closure; the ledger determines global progress. No existing file is withdrawn or deleted.

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses`
- `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`
- `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre`
- `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`
- `Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors`
- `Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient`
- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`
- `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank`
- `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation`
- `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix`
- `Sheaf.AlgebraicGeometry.CondensedFieldRankDescent`
- `Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars`
- `Sheaf.AlgebraicGeometry.CondensedQbarPointBasis`
- `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis`
- `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisPushforward`
- `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisSections`
- `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnit`
- `Sheaf.AlgebraicGeometry.CondensedQbarScalarBasisUnitOfSections`
- `Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse`
- `Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree`
- `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixElimination`
- `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm`
- `Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm`
- `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs`
- `Sheaf.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairsAux`
- `Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound`
- `Sheaf.AlgebraicGeometry.LocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`
- `Sheaf.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension`
- `Sheaf.CategoryTheory.AdjunctionSquareExchange`
- `Sheaf.CategoryTheory.AlgebraicInverseImage`
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`
- `Sheaf.CategoryTheory.CoefficientPushCopowerCriterion`
- `Sheaf.CategoryTheory.DenseSubsiteModuleRestriction`
- `Sheaf.CategoryTheory.InternalSectionModuleFlat`
- `Sheaf.CategoryTheory.SheafPullbackForgetComparison`
- `Sheaf.CategoryTheory.Sites.InverseImageLocalFamilies`
- `Sheaf.CategoryTheory.Sites.LocallyBijectiveFiniteLimit`
- `Sheaf.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact`
- `Sheaf.LinearAlgebra.FiniteIndexSplitting`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrCore`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.Paper.CondensedCoefficientPointUnitPasting`
- `Sheaf.Paper.CondensedQbarCoefficientConstruction`
- `Sheaf.Paper.CondensedQbarFieldCoefficientSquare`
- `Sheaf.Paper.CondensedQbarFieldEvaluationLinearity`
- `Sheaf.Paper.CondensedQbarFieldFiberExtension`
- `Sheaf.Paper.CondensedQbarFieldPointCoefficientValue`
- `Sheaf.Paper.CondensedQbarFunctionCoefficients`
- `Sheaf.Paper.CondensedQbarFunctionPresentations`
- `Sheaf.Paper.CondensedQbarLfpCoverComposition`
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`
- `Sheaf.Paper.CondensedQbarLfpMatrixRefinement`
- `Sheaf.Paper.CondensedQbarScalarPullback`
- `Sheaf.Paper.ConstructibleCokernelsExtensions`
- `Sheaf.Paper.ContinuousChartSchemeNaturality`
- `Sheaf.Paper.ContinuousCoefficientRealizations`
- `Sheaf.Paper.ContinuousIntegralCoefficients`
- `Sheaf.Paper.ContinuousRegularFunctions`
- `Sheaf.Paper.FiniteBiproductPivot`
- `Sheaf.Paper.FiniteContinuousUltrametricPivot`
- `Sheaf.Paper.FiniteDiscreteCondensedRing`
- `Sheaf.Paper.FiniteDiscreteSchemeRing`
- `Sheaf.Paper.GeometricFieldProEtaleEvaluation`
- `Sheaf.Paper.GeometricFieldProfiniteDenseSubsite`
- `Sheaf.Paper.IntegralConstructibleKernels`
- `Sheaf.Paper.IntegralLfpEventualFreeImage`
- `Sheaf.Paper.IntegralLfpFiniteQuotientCharts`
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`
- `Sheaf.Paper.IntegralMatrixAnalyticCover`
- `Sheaf.Paper.IntegralMatrixAnalyticData`
- `Sheaf.Paper.IntegralMatrixCoefficientTransport`
- `Sheaf.Paper.IntegralMatrixEntryProperties`
- `Sheaf.Paper.IntegralMatrixFunctionsPullback`
- `Sheaf.Paper.IntegralMatrixPivotCover`
- `Sheaf.Paper.IntegralMatrixPointwiseRank`
- `Sheaf.Paper.IntegralMatrixZeroNeighborhood`
- `Sheaf.Paper.IntegralRegularCoefficientPullback`
- `Sheaf.Paper.IntegralRegularRationalUnit`
- `Sheaf.Paper.IntegralScalarContractive`
- `Sheaf.Paper.InternalModuleAbEquivalence`
- `Sheaf.Paper.InverseImageModuleFlat`
- `Sheaf.Paper.ModuleObjectFreeGenerators`
- `Sheaf.Paper.PointLanAffineEvaluation`
- `Sheaf.Paper.PointLanFiniteProducts`
- `Sheaf.Paper.ProEtalePointComponentsMaps`
- `Sheaf.Paper.ProEtaleSheafificationWcontractibleSections`
- `Sheaf.Paper.ProfinitePointPullback`
- `Sheaf.Paper.ProfiniteTestObjectFunctor`
- `Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra`
- `Sheaf.Paper.RegularExtensionComparison`
- `Sheaf.Paper.SectionModuleAlgebraicInverseImage`
- `Sheaf.RingTheory.DimensionQuasiFiniteOverPolynomialAlgebra`
- `Sheaf.RingTheory.QuasiFiniteAtPrime`
- `Sheaf.RingTheory.QuasiFiniteFourRings`
- `Sheaf.RingTheory.QuasiFiniteLocalDimension`
- `Sheaf.Topology.DimensionSupremumLocalDimensions`
- `WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal`
- `WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex`
- `WeilConjectures.Algebra.Homology.ResolutionByClass`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyTrivial`
- `WeilConjectures.AlgebraicGeometry.GenericFiniteness`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.Limit`
- `WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FiniteApproximation`
- `WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Affine`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Coherent.Etale`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`
- `WeilConjectures.AlgebraicGeometry.ProEtale.LocalProperties`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Basic`
- `WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Sites.AffineRefinement`
- `WeilConjectures.Blowup.AdmissibleBlowup`
- `WeilConjectures.Blowup.Affine.BaseChange`
- `WeilConjectures.Blowup.Affine.BaseChangeSurjectivity`
- `WeilConjectures.Blowup.Affine.Defs`
- `WeilConjectures.Blowup.Affine.Functoriality`
- `WeilConjectures.Blowup.Affine.Localization`
- `WeilConjectures.Blowup.Affine.Principalization`
- `WeilConjectures.Blowup.Affine.Proper`
- `WeilConjectures.Blowup.Affine.ReesGrading`
- `WeilConjectures.Blowup.BaseChange`
- `WeilConjectures.Blowup.BlowupUniversal`
- `WeilConjectures.Blowup.Complement`
- `WeilConjectures.Blowup.Density`
- `WeilConjectures.Blowup.DisjointnessBlowup`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.AffineSpace`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.ChartPreimage`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.Closedness`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.CommonDenominator`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.Coordinates`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.Gluing`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.GraphClosedness`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.Lift`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.QuasiAffine`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.QuasiAffineHom`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.Slope`
- `WeilConjectures.Blowup.EliminationOfIndeterminacy.ZeroLocus`
- `WeilConjectures.Blowup.Extension`
- `WeilConjectures.Blowup.FiniteDegree`
- `WeilConjectures.Blowup.FiniteDegree.Algebra`
- `WeilConjectures.Blowup.FiniteDegree.ChartIdeal`
- `WeilConjectures.Blowup.FiniteDegree.ChartProbe`
- `WeilConjectures.Blowup.FiniteDegree.Generation`
- `WeilConjectures.Blowup.FiniteDegree.LocalAlgebra`
- `WeilConjectures.Blowup.FiniteDegree.Main`
- `WeilConjectures.Blowup.FiniteDegree.UniformNumerator`
- `WeilConjectures.Blowup.Gluing`
- `WeilConjectures.Blowup.GraphQuasiFinite`
- `WeilConjectures.Blowup.PartialSectionExtension`
- `WeilConjectures.Blowup.PartialSectionExtensionReduction`
- `WeilConjectures.Blowup.Principalization`
- `WeilConjectures.Blowup.Proper`
- `WeilConjectures.Blowup.QuasiAffineGeneral`
- `WeilConjectures.Blowup.QuasiAffineGeneralReduction`
- `WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat`
- `WeilConjectures.CategoryTheory.Comma.ArrowRefinement`
- `WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal`
- `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing`
- `WeilConjectures.CategoryTheory.Pro.Basic`
- `WeilConjectures.CategoryTheory.Pro.Generating`
- `WeilConjectures.CategoryTheory.Pro.PresheafColimit`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient`
- `WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal`
- `WeilConjectures.CategoryTheory.Sites.Point.Flat`
- `WeilConjectures.Compactification.Affine`
- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.Compactification.BoundaryPreparation`
- `WeilConjectures.Compactification.BoundarySeparationData`
- `WeilConjectures.Compactification.CommonModification`
- `WeilConjectures.Compactification.Constructions`
- `WeilConjectures.Compactification.EliminationOfIndeterminacy`
- `WeilConjectures.Compactification.FinitePresentation`
- `WeilConjectures.Compactification.FiniteTypeDirected`
- `WeilConjectures.Compactification.FiniteTypeExtension`
- `WeilConjectures.Compactification.GraphExtension`
- `WeilConjectures.Compactification.IdealSheafPower`
- `WeilConjectures.Compactification.ImageTransport`
- `WeilConjectures.Compactification.IsomorphismNearClosure`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Compactification.Noetherian`
- `WeilConjectures.Compactification.Over`
- `WeilConjectures.Compactification.ProjectiveSpace`
- `WeilConjectures.Compactification.StrictTransform`
- `WeilConjectures.Compactification.StrictTransformBlowup`
- `WeilConjectures.Compactification.TwoOpen`
- `WeilConjectures.Compactification.TwoOpenComparison`
- `WeilConjectures.Compactification.TwoOpenSetup`
- `WeilConjectures.Compactification.ValuativeCriterion`
- `WeilConjectures.ConstructibleSheaf.ConstantFiniteDual`
- `WeilConjectures.ConstructibleSheaf.ConstantFiniteFreeDualNaturality`
- `WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernel`
- `WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernelAux`
- `WeilConjectures.ConstructibleSheaf.ConstantModuleDual`
- `WeilConjectures.ConstructibleSheaf.DualLocallyConstant`
- `WeilConjectures.ConstructibleSheaf.DualStalk`
- `WeilConjectures.ConstructibleSheaf.EtaleDualRestriction`
- `WeilConjectures.ConstructibleSheaf.FiniteConstantModel`
- `WeilConjectures.ConstructibleSheaf.FreeLifting`
- `WeilConjectures.ConstructibleSheaf.Monoidal`
- `WeilConjectures.ConstructibleSheaf.MonoidalParts`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Basic`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Constructions`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation`
- `WeilConjectures.Mathlib.Algebra.DirectSum.Internal`
- `WeilConjectures.Mathlib.Algebra.Homology.Embedding.HomEquiv`
- `WeilConjectures.Mathlib.Algebra.MvPolynomial.Basic`
- `WeilConjectures.Mathlib.Algebra.Polynomial.Laurent`
- `WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Cover.Open`
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Gluing`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.IsIso`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Preimmersion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Properties`
- `WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks`
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Restrict`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Scheme`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.AffineEtale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.ZariskisMainTheorem`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective`
- `WeilConjectures.Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Enriched.FunctorCategory`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport`
- `WeilConjectures.Mathlib.CategoryTheory.Galois.IsFundamentalgroup`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Subcategory`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Coverage`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.DenseSubsite.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Finite`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.MorphismProperty`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Sheafification`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Sieves`
- `WeilConjectures.Mathlib.CategoryTheory.Whiskering`
- `WeilConjectures.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`
- `WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank`
- `WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement`
- `WeilConjectures.Mathlib.RingTheory.Filtration`
- `WeilConjectures.Mathlib.RingTheory.FinitePresentation`
- `WeilConjectures.Mathlib.RingTheory.Finiteness.Descent`
- `WeilConjectures.Mathlib.RingTheory.Flat.Equalizer`
- `WeilConjectures.Mathlib.RingTheory.Flat.Localization`
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`
- `WeilConjectures.Mathlib.RingTheory.GradedAlgebra.RingHom`
- `WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Maps`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Operations`
- `WeilConjectures.Mathlib.RingTheory.Ideal.Quotient.Operations`
- `WeilConjectures.Mathlib.RingTheory.Ideal.RegularPrincipal`
- `WeilConjectures.Mathlib.RingTheory.IsTensorProduct`
- `WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial`
- `WeilConjectures.Mathlib.RingTheory.KrullDimension.Zero`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.Basic`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Basic`
- `WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
- `WeilConjectures.Mathlib.RingTheory.Localization.Finiteness`
- `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous`
- `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Ideal`
- `WeilConjectures.Mathlib.RingTheory.Nakayama`
- `WeilConjectures.Mathlib.RingTheory.NoetherNormalization`
- `WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian`
- `WeilConjectures.Mathlib.RingTheory.ReesAlgebra`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian`
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.Basic`
- `WeilConjectures.Mathlib.RingTheory.TensorProduct.DirectLimitFG`
- `WeilConjectures.Mathlib.RingTheory.TotallySplit`
- `WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring`
- `WeilConjectures.Mathlib.RingTheory.Valuation.ValuationSubring`
- `WeilConjectures.RingTheory.Dehomogenization`
- `WeilConjectures.RingTheory.QuasiFiniteAtPrime`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.KFlat`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`
- `WeilConjectures.SixFunctors.OpenClosed.Conservative`
- `WeilConjectures.SixFunctors.OpenClosed.Points`
- `WeilConjectures.SixFunctors.OpenClosed.Supported`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule`
- `WeilConjectures.Topology.DimensionSupremumLocalDimensions`
- `WeilConjectures.Topology.SpectralSpace.ConstructibleSeparation`

## Where the brief, the DAG or earlier work was wrong

The assigned node lists `det-def-localizing-closure-ctf-equals-bc`, `det-ambient-ind-derived-sums`, `sk-lem-proper-unbounded-window-ii`, and `det-prop-int-compactness-direct-sums` without Lean attachments or Mathlib matches. Consequently the listed plan cannot simply be translated by importing those declarations. The existing generic ordinary qcqs continuity theorem supplies a stronger bounded-below input and removes the finite-interval sum induction. The remaining uniform truncation assertion is isolated with its actual hull hypothesis rather than asserted for arbitrary ambient sheaves: the latter cohomological-dimension assertion is false in this library's pro-étale setting.

The generic node `lem-sfb-left-complete-heart-upper-bound` advertises `Sheaf.CategoryTheory.Triangulated.LeftCompleteHeartUpperBound`, but its Lean file is absent from this checkout. The delivery cites the existing node in the mathematical argument and does not duplicate its statement. For the remaining hole, the rational heart bound is `sk-lem-proper-heart-bound`; the integral bound and tail passage are clauses (1)-(2) of `det-prop-int-compactness-direct-sums`; hull containment uses `det-ambient-ind-derived-sums` and `det-ambient-ind-derived-triangulated`. These identify the remaining inputs more precisely than a general appeal to an unbounded continuity theorem.

The existing module docstring describes the original coefficient-by-coefficient plan. Its declaration and source remain unchanged; the updated DAG proof and this report describe the shorter Lean route actually used. No mathematical statement is disputed.

## New nodes

`lem-sfb-adic-proper-bounded-below-coproducts` is attached to `Sheaf.AlgebraicGeometry.EllAdicProperBoundedBelowCoproducts`. It is proved, with no local holes, from existing continuity and derived coproduct infrastructure. It serves the common-lower-bound truncated-family step of the proper identity-compactification proof. The continuity input `lem-weil-pbc-condensed-qcqs-pushforward-continuity` is an already formalized tool from the proper-base-change unit; the present unit has no equally general ordinary bounded-below continuity statement. No maintainer tool approvals are added or changed.

`lem-sfb-adic-proper-truncation-bound` is attached to `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound`. Its remaining sorry is strictly the geometric upper-amplitude bound on discarded lower tails; it says nothing about sums or comparison maps. The truncation-triangle passage from that bound to the comparison isomorphism is formalized completely in the assigned module. Its source is the arbitrary-complex/window argument of `sk-lem-proper-unbounded-window` and integral clauses (1)-(2) of `det-prop-int-compactness-direct-sums`. It still needs the heart bound, hull containment and Milnor/left-completeness passage described above. Actual LeanSearch, LeanFinder, Loogle and source-grep queries are logged and recorded in both new nodes, covering the three required search kinds. The assigned node's proof, proof dependencies and proof origin are updated; all other fields are kept.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
