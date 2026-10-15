# CategoryTheory.imagePresheaf_sheafification_iso

## Reason

The former independent value universe is false under HasWeakSheafify alone, rather than
merely missing a Mathlib instance. The earlier reviewed correction of
CategoryTheory.sheafification_sections_local already records this item as requiring the
same size repair (coord/reports/P3/Sheaf.Paper.SiteSheafificationSectionsLocal.md).
Use Type (max u v) for C : Type u with Category.{v} C, the standard set-valued plus
construction convention. Keep both conclusions and prove them entirely from Mathlib.
This is an explicitly corrected intermediate statement, not a proof of its false former
signature. No target declaration or definition changes, so no target definition review
is reopened. There are no data definitions in this delivery.

For completeness, the counterexample from coord/reports/U2/Sheaf.Paper.SiteSheafificationSectionsLocal.md
applies directly. Choose an infinite alphabet A larger than every Type w set, and let B
be the complete Boolean algebra of regular opens of A^N. Give the poset B the join-cover
site. Any small-valued sheaf H is subterminal: if two sections differ, restrict to a
nonzero Boolean piece where they differ on every nonzero subpiece, choose a finite
coordinate cylinder there, and partition it into A pairwise disjoint next-coordinate
cylinders. Independently choosing either section on each piece gives an injection
(A -> Bool) into a section type of H. Cantor contradicts smallness. Empty intersections
cause no compatibility issue because the empty cover makes H(bottom) a singleton.
Small sheaves nevertheless have a reflector: take the support of a presheaf inside the
terminal presheaf, then its sheaf closure. It is small (values are subsingletons), and
maps into any small sheaf factor uniquely, since every such sheaf is subterminal.
Thus the constant presheaf inclusion 1 -> 2 becomes the identity of the terminal sheaf
after weak sheafification. It is not locally surjective: the second element is absent
on every restriction, so its image sieve at the nonzero top is empty and not covering.

Sources: Stacks Sites, Tags [00WK](https://stacks.math.columbia.edu/tag/00WK),
[00WJ](https://stacks.math.columbia.edu/tag/00WJ), and
[00WN](https://stacks.math.columbia.edu/tag/00WN), read online because the repository's
literature/stacks-project/sites.tex is absent. The mathematical proof follows the ordinary
set-valued sheafification in these sources. The large-site counterexample is the existing
project review argument and is not asserted to be formalized in Lean.

## Old

```lean
theorem imagePresheaf_sheafification_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type w)] {F G : Cᵒᵖ ⥤ Type w} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type w)).map φ)) :
    Presheaf.IsLocallySurjective J φ ∧
      IsIso ((presheafToSheaf J (Type w)).map (Subfunctor.range φ).ι)
```

The declaration used independent universes u, v, w and had proof `by sorry`.

## New

```lean
theorem imagePresheaf_sheafification_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type (max u v))] {F G : Cᵒᵖ ⥤ Type (max u v)} (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type (max u v))).map φ)) :
    Presheaf.IsLocallySurjective J φ ∧
      IsIso ((presheafToSheaf J (Type (max u v))).map (Subfunctor.range φ).ι)
```

The declaration uses universes u, v and its complete proof is in the delivered module.

## Users

The downstream scan reported 503 modules; the table lists them all. A textual search
finds no declaration application outside the defining module. The sole direct importer is
Sheaf.Paper.CechNerveFreeHomology (held by T3); its unchanged original compiled against
the corrected module. A separate compiled example checks the exact planned application
for C : Type u, SmallCategory C, Type u-valued presheaves. No downstream adaptation is
forced, and none is included. The sole DAG citer
lem-weil-pbc-cech-nerve-free-homology retains its full statement and proof route because
its site and value universe are u. No unit statement or realized step is bypassed;
dag/units/sk-prop-h2.json has this node in none of its realized lists.

| module | group holding it | effect |
|---|---|---|
| Comparator.Weil.Solution | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineCurveCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSupportVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantFiniteComparison | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleFiniteSurjectionCancellation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImagesComp | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModificationTransfer | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedCohomologyContinuity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyClassDescent | H1 | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportBaseChangeQcqs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactSupportOpenClosedTriangle | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekQcqsComposition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleShriekRelativeMayerVietoris | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.GeometricFiberFinite | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LerayBounded | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ModificationExtensionZero | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteGeometricPoint | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectionFormulaFiniteObjectwise | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveConstructibleHigherDirectImages | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveConstant | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSmoothCurveFiniteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBoundedConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperCaseConstructibility | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperConstructibleHigherDirectImages | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperDerivedDirectImageCoproducts | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCopowers | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperLocallyAcyclicSpecialization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonComposition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenComparisonIso | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperProjectionFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChangeModN | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDimensionOneInduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FibrewiseCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit | G4 | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperPrimeSpecialization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionSheafProperBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.CechNerveFreeHomology | T3 | Direct importer; original compiles against corrected dependency; Type u on SmallCategory C fits. |
| Sheaf.Paper.HypercoverCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyAbelian | N1 | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverCohomologyModule | N3 | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.HypercoverFreeResolution | R2 | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| TargetsCheck | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension | P1 | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionLimit | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceAdjunction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicalSmoothness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.SupportedClassMapRestriction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.ThomClass | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Basic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.KummerClass | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.EtaleCohomology.TateTwist.Normalized | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Composition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Dualizing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.BoundedConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupportBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteComparison | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Modification | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Projective | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ProjectiveCurve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Proper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.TargetLocal | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Localization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocallyConstantInvertible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionAssoc | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Point | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Rational | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Shift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ShiftAssoc | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SingleDelta | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.TorSheaf | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Triangulated | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriek | XRdbb7091a3d1839f4 | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsComposition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Pairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Shift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Basic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexample | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.AmbientCounterexampleCoproducts | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.DualPerfect | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Duality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Finiteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.HomComparison | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationConstructible | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LocalizationFiniteTor | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriekIndependence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormulaExtendScalars | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ScalarExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Stability | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ExceptionalAdjoint | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Adic | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusLift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicFrobeniusTrace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicRange | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AdicSystem | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.AffineReduction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Correspondence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Curve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FiniteModel | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.FixedPoints | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Iterate | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.KernelPushforward | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.LocalFrobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Localization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Main | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ModelRestriction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Pairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.Perfectness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperCurve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.ProperPushforward | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardFibres | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.PushforwardStep | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.RelativeAffineLine | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceClass | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceFormulaHolds | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.TraceFormula.TraceMap | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.Statement | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.SixOperations | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No declaration use; statement and definitions unaffected; no adaptation. |

## Status

landed 20261015T221553-L-2623949 2026-10-15 (merge of deliver/A4/Sheaf.Paper.ImagePresheafSheafificationIso)
