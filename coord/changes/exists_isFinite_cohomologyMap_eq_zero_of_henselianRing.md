# AlgebraicGeometry.Etale.exists_isFinite_cohomologyMap_eq_zero_of_henselianRing

## Reason

Reviewer X-4d8e7, E2: STATEMENT-DISPUTED; the theorem is false and must not remain
as a sorry-backed public theorem. Take A=ℂ[t], I=0 (a henselian pair), Λ=ℤ/2,
X=𝔸¹_ℂ, Z={0,1}, j:X\Z→X and C=j!Λ. The boundary c of (0,1) under
0→j!Λ→Λ_X→Λ_Z→0 is nonzero in H¹(X,C), since global sections of Λ_X
are constant. A finite h:V→X with monic unit for C has nonempty generic fibre:
otherwise the generic stalk of h_*h^*C is zero while that of C is Λ.
The closure W of a point above the generic point is irreducible, closed, finite
and surjective over X, hence connected and meeting both endpoint fibres.
The pulled-back boundary on W is still nonzero: a locally constant function on
connected W cannot restrict to 0 above 0 and 1 above 1. Thus c cannot vanish
on V. This refutes the declaration even for I=0 and q=1.

## Old

```lean
theorem exists_isFinite_cohomologyMap_eq_zero_of_henselianRing [Finite Λ] {A : Type u}
    [CommRing A]
    (I : Ideal A) [HenselianRing A I]
    (C : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C]
    {q : ℕ} (hq : 0 < q)
    (c : Sheaf.H
      (((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))^*[AddCommGrpCat.{u + 1}]).obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj C)) q) :
    ∃ (V : Scheme.{u}) (h : V ⟶ Spec (.of A)), IsFinite h ∧ LocallyOfFinitePresentation h ∧
      cohomologyMap (pullback.fst (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) h) _ q c =
        0 ∧
      Mono ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).unit.app C)
```

The entire finite-cover docstring, disputed comment and sorry theorem are removed,
as is its two-line entry under Main statements.

## New

No replacement declaration. Retire `lemma-weil-pbc-finite-cover-killing`:
its active `lean` attachment is null, its invalid proof and proof_deps are empty,
and proof_origin records the counterexample and retirement. The historical
statement, blueprint import and audit records remain historical records; they
no longer attach a Lean theorem or provide an asserted proof. No target changes.

## Users

The whole-library downstream.py search on 2026-10-13 reports 147 downstream
modules and one textual user, Gabber itself (its Main statements entry).
An independent rg of every library .lean file also finds only that entry and
the declaration in Gabber. No external proof uses the removed theorem.
The full downstream inventory follows; no adaptation is required anywhere.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Remove false declaration and documentation; no surviving proof uses it. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No occurrence of removed declaration; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No occurrence of removed declaration; no adaptation. |
| TargetsCheck | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | X3 | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No occurrence of removed declaration; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No occurrence of removed declaration; no adaptation. |

## Status

landed 20261012T194127-L-460521 2026-10-12 (merge of deliver/N2/WeilConjectures.SixFunctors.Etale.Gabber)
