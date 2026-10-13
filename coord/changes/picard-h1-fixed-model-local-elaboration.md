# picard_h1_fixed_model_comparison: local elaboration attributes

## Reason

The proof uses local irreducibility for the heavy structure-sheaf cohomology
constructions, so elaboration keeps their stated group types folded. The static
preflight classifies any added attribute command as an interface change and
requires this record. These are local attributes in the item module, not edits to
the definitions or exported attributes. No target meaning changes or target
statement review is reopened. No existing module is adapted.

## Old

There was no local irreducibility command. The existing theorem signature was:

```lean
theorem picard_h1_fixed_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K)) :
    ∃ (q : ℕ) (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      (∀ a : Γ(W, U),
        b (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z)
```

## New

The theorem signature is exactly:

```lean
theorem picard_h1_fixed_model_comparison
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    {X S : Scheme.{v}} (f : X ⟶ S) {n : ℕ}
    (Xi : Fin n → Scheme.{v}) (fi : ∀ i, Xi i ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    [∀ i, Flat (fi i)] [∀ i, IsProper (fi i)] [∀ i, LocallyOfFinitePresentation (fi i)]
    (ui : ∀ i, Xi i ⟶ X) (hui : ∀ i, ui i ≫ f = fi i)
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hOi : ∀ i, ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Scheme.Modules.exists_tensorPullbackAdjunction (pullback.snd (fi i) g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (htrivial : ∀ i, Nonempty
      ((Modules.tensorPullback (pullback.fst (fi i) (U.ι ≫ k))).obj
        ((Modules.tensorPullback (ui i)).obj L) ≅
        SheafOfModules.unit (pullback (fi i) (U.ι ≫ k)).ringCatSheaf))
    (m : ℕ) (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) j w)))))
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj
      ((schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))) ≅
        DerivedCategory.Q.obj K)) :
    ∃ (q : ℕ) (b : (Fin m → Γ(W, U)) →ₗ[Γ(W, U)] (Fin q → Γ(W, U))),
      (∀ a : Γ(W, U),
        b (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a))) = 0) ∧
          let p := RingHom.ker (W.evaluation U w hwU).hom
          letI : p.IsPrime := RingHom.ker_isPrime (W.evaluation U w hwU).hom
            ∃ (α : (p.ResidueField ⊗[Γ(W, U)] (Fin m → Γ(W, U))) ≃+
                Sheaf.H (structureSheafAb (pullback f (S.fromSpecResidueField s))) 1)
              (β : (p.ResidueField ⊗[Γ(W, U)] (Fin q → Γ(W, U))) →+
                (∀ i, Sheaf.H
                  (structureSheafAb (pullback (fi i) (S.fromSpecResidueField s))) 1)),
              ∀ z, β ((b.baseChange p.ResidueField) z) = fun i ↦
                structureSheafCohomologyPullback
                  (((Over.pullback (S.fromSpecResidueField s)).map
                    (Over.homMk (U := Over.mk (fi i)) (V := Over.mk f)
                      (ui i) (hui i))).left) 1 (α z)
```

The new command preceding the theorem is:

```lean
attribute [local irreducible] structureSheafAb structureSheafCohomologyPullback
```

The scoped options immediately preceding its declaration affect only proof
elaboration. The definition bodies, statement imports, universes and binders are
unchanged. The new coordinate helper is private and does not occur in any public
signature. The two added geometric lemmas have their own modules and DAG nodes.

## Users

`tools/downstream.py` found 161 transitive importers; its `--uses
picard_h1_fixed_model_comparison` scan found only
`Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel` as a caller outside the item.
Its existing call applies the same unchanged signature. Every transitive importer
is listed here with the local snapshot's holder. None requires adaptation, since
local reducibility attributes do not propagate to importers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | H1 | Local proof elaboration only; unchanged signature. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No adaptation; local attributes are not exported. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No adaptation; local attributes are not exported. |
| TargetsCheck | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No adaptation; local attributes are not exported. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No adaptation; local attributes are not exported. |

## Status

landed 20261013T145120-L-696026 2026-10-13 (merge of deliver/H1/Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison)
