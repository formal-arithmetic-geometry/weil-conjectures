# sectionRing_veronese_fraction_formula

## Reason

Repair of reviewer X-9f6b3, head 9f6b3ae93, C3/E5 point 4. Bare Nonempty of
additive equivalences does not specify their action on generators. The reviewer
explicitly required the canonical quotient equivalence and its formula, together
with the forced user adaptation. The replacement construction extends the actual
summand maps to a direct sum, proves surjectivity, identifies the relation subgroup
with its kernel, and uses the first isomorphism theorem. The unique inverse of a
fixed bijective map is allowed by AGENTS.md section 5. All data are explicit; only
the kernel proof is postponed as a named sourced theorem, in its own module/node.

The new hole is equality between the kernel of a specified constructed homomorphism
and a specified relation subgroup. It is a strict part of the quotient argument;
it says neither that an unspecified equivalence exists nor what it does to a generator.
The formula itself is proved by evaluating the quotient map and cancelling the
numerator isomorphism and injection.

## Old

```lean
theorem sectionRing_veronese_fraction_formula
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d)
    (e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
    (he : e = Classical.choice (sectionRing_veronese_fraction_core X L d s)) :
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property) =
      sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
        ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
          L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d)))
```

The original user proof chooses its witness with:

```lean
  let e := Classical.choice (sectionRing_veronese_fraction_core X L d s)
```

## New

```lean
theorem sectionRing_veronese_fraction_formula
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d)
    (e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
    (he : e = sectionRingVeroneseFractionEquiv X L d s) :
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property) =
      sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
        ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
          L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d)))
```

The added public definition is:

```lean
noncomputable def sectionRingVeroneseFractionEquiv
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) :=
  (QuotientAddGroup.liftEquiv
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (sectionRingVeroneseFractionMap_surjective X L d s)
    (sectionRingVeroneseFractionMap_kernel X L d s)).symm
```

Its public dependencies are the explicitly constructed map in
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionMap` and the kernel theorem in
`Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionKernel`. The old public import
of `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` is removed from the
formula module, and the kernel module is publicly imported because the exposed
definition's body needs its proof. Other existing public imports are kept.

The user proof now uses:

```lean
  let e := sectionRingVeroneseFractionEquiv X L d s
```

## Users

`tools/downstream.py ... --uses sectionRing_veronese_fraction_formula` finds only
the item and `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` as textual users.
The table also records every transitive importer, for completeness. The adapted
module is unclaimed in this checkout. Its old proof compiles against the baseline
but fails against the changed formula, with the following error at line 61:

```text
Application type mismatch: The argument rfl has type ?m.115 = ?m.115
but is expected to have type e = sectionRingVeroneseFractionEquiv X L d s
in the application sectionRing_veronese_fraction_formula X L d s e rfl
```

Only line 60 changes. This supplies exactly the witness required by the repaired
formula, so line 61 compiles again. No other line, signature, or visibility of the
unheld module changes. Its original proof-only Core import is retained to obey
forced-line-only adaptation; it is no longer used by the adapted proof.
No target signature or definition used in a target statement changes. The existing
existence-and-formula theorem has exactly its previous statement, and all higher
users retain their mathematical meaning. The unit's realized statement and steps
are untouched.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula` | R3 | Held item: replace the witness equality and construct the canonical equivalence. |
| `Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjLocalChart` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.AmpleProjOpen` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantInvariance` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperCohomology` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ProperProjective` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.DimOneQuasiProjective` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.GluedComponentAffineSection` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.IsProperOrIsAffine` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingLocalizationBijective` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractions` | unclaimed | Forced adaptation: only line 60 changes the local witness; all signatures and visibility stay identical. |
| `Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.AlgebraicGeometry.TorsionAssembly` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `Sheaf.Paper.OpenCurveEtaleLerayLowDegree` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `TargetsCheck` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Affine` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.Compactification` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.PoincareDuality.Transport` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Basic` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.EtaleCohomology.Purity.Smooth.Transport` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.KernelTransform` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.AffineSpace.Transform` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Defs` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Inversion` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Properties` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Properties.BaseLinear` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.FourierTransform.Properties.Stalk` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine` | ORCHESTRA | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Composition` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Orientation` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Package` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.Supports` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.TensorHom` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilComplex` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.Perfect` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |
| `WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition` | unclaimed | Imports only: no use of the changed formula; no statement or definition changes and no adaptation. |

## Status

landed 20261013T040759-L-3952109 2026-10-13 (merge of deliver/R3/Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsFormula)
