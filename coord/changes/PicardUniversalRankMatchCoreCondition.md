# PicardUniversalRankMatchCoreCondition

## Reason

Repair E2 from reviewer X-71f31 (head 71f319edd). The previous definition required
only equal universal ranks of the direct images of E and its dual. It did not constrain
the rank of E. For X = Spec k disjoint union Spec k, S = T = Spec k, g = identity and
E = O_X, both direct images have rank 2 under every base change while E has rank 1.
Thus the old compatibility implication was false. Use an abbreviation of PicardUniversalRankMatch, thereby adding exactly its bundle-rank
clause and preserving both existing theorem signatures. This also follows the rule that
two definitions of one notion are consolidated rather than maintained separately.
This strengthens the core predicate to the intended three-clause condition; it does not
change PicardUniversalRankMatch or any target statement. The old two-component example
now fails the corrected core condition as well as the full condition.

The existence theorem now asserts representability of the corrected condition and remains
unproved. Its argument must first fix E's rank on open-and-closed base strata, then build
the two direct-image loci for that same rank. Compatibility becomes definitional.
Source: [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP).

## Old

```lean
def PicardUniversalRankMatchCoreCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
    ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
              (Modules.dual E)))) r
```

## New

```lean
abbrev PicardUniversalRankMatchCoreCondition {X S T : Scheme.{u}} (f : X ⟶ S)
    (E : X.Modules) (g : T ⟶ S) : Prop :=
  PicardUniversalRankMatch f E g
```

## Users

The read-only downstream.py query found 166 transitive importers. The
whole-word usage query found the definition only in its own module; compatibility is
used by PicardUniversalRankMatchLocusCore. The table lists every downstream module plus
the changed module. Holders are the local claim snapshot at repair time. No module needs
a forced adaptation: the downstream core theorem compiles unchanged, and its public
statement uses the unchanged PicardUniversalRankMatch. All five Challenge.lean target
statements are preserved. Any target interpretation review whose definitions transitively
use this changed predicate must be reopened under stages/2-statements.md §4; no target
text is edited. Transitive import alone is not a change in the meaning of a statement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | W4 | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Existing proof uses compatibility; signature and meaning unchanged; unchanged source compiled against the corrected dependency. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | G3 | Definition gains the bundle-rank clause; existence has corrected meaning and stays sorry; compatibility is rfl. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| TargetsCheck | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer; no textual use of the changed definition; existing statements and proofs unchanged. |

## Status

landed 20261013T024034-L-3334430 2026-10-13 (merge of deliver/G3/Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank)
