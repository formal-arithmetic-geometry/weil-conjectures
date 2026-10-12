# strictHenselian_zariski_etale_comparison

## Reason

Repair review point 4 (E2 / H3). The old signature universally quantified a
continuous functor and an arbitrary cohomology map family. For an algebraically
closed field and the constant integer sheaf, the zero map in degree zero
contradicts its conclusion. The node already specifies the open-subscheme
inclusion and the canonical pullback-then-counit map; the Lean signature did not.

The correction follows Stacks Tag 09AX and the defining pullback characterization
of `CategoryTheory.siteCohomology_pullback`. `hi_inclusion` identifies the forgetful
composite with `X.restrictFunctor`. `hfstar` fixes pullback by naturality,
compatibility with connecting morphisms, and its degree-zero unit map, and `hc`
identifies `c` with that pullback followed by the counit. The additive inverse-image
instance makes the short-complex compatibility well typed; it is structural data
of this morphism of sites, not an acyclicity or invertibility assumption.

The conclusion remains invertibility of this particular map in every degree.
There is no `IsIso c` hypothesis and no replacement by unspecified isomorphisms.
No target statement or definition changes, so no target definition review reopens.
The mathematical DAG statement was already correct and remains verbatim; only its
`lean.statement` and audit note change. No `statement_change` record is appropriate
because there is no change to the node's mathematical `statement`.

## Old

```lean
theorem strictHenselian_zariski_etale_comparison
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : ∀ q : ℕ,
      Sheaf.H'
          ((i.sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F)
          q ⊤ ⟶
        Sheaf.H' F q (i.obj ⊤)) :
    ∀ q : ℕ, IsIso (c q)
```

## New

```lean
theorem strictHenselian_zariski_etale_comparison
    {X : Scheme.{u + 1}}
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    (fstar : ∀ (p : ℕ) (V : X.Opens)
      (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}),
      Sheaf.H' A p V ⟶
        Sheaf.H' ((sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj A)
          p (i.obj V))
    (hfstar : (∀ (p : ℕ) (V : X.Opens) (A A' : Sheaf (Opens.grothendieckTopology X.carrier)
      AddCommGrpCat.{u + 1}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p).map φ).app
          (op V) ≫
            fstar p V A' =
          fstar p V A ≫
            ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology p).map
              ((sheafPullback i AddCommGrpCat.{u + 1}
                (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map φ)).app
                  (op (i.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}))
        (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback i AddCommGrpCat.{u + 1}
          (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)).ShortExact)
        (p : ℕ) (V : X.Opens) (x : Sheaf.H' S.X₃ p V),
        (fstar (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fstar p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : X.Opens) (A : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})
        (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fstar 0 V A).hom x)).hom.app (op (i.obj V))).hom
            (((toSheafify X.smallEtaleTopology
              (yoneda.obj (i.obj V) ⋙ AddCommGrpCat.free)).app (op (i.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (i.obj V)))) =
          (((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).unit.app A).hom.app
              (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify (Opens.grothendieckTopology X.carrier)
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V))))))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : ∀ q : ℕ,
      Sheaf.H'
          ((i.sheafPushforwardContinuous (AddCommGrpCat.{u + 1})
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F)
          q ⊤ ⟶
        Sheaf.H' F q (i.obj ⊤))
    (hc : ∀ q : ℕ, c q =
      fstar q ⊤
          ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F) ≫
        ((Sheaf.cohomologyPresheafFunctor X.smallEtaleTopology q).map
          ((sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
            (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).counit.app F)).app
              (op (i.obj ⊤))) :
    ∀ q : ℕ, IsIso (c q)
```

## Users

`tools/downstream.py Sheaf.Paper.StrictHenselianZariskiEtaleComparison --uses
strictHenselian_zariski_etale_comparison` found 140 transitive importers,
and no use of this declaration outside its own module. Both direct importers,
`Sheaf.Paper.GabberCriterion` and `Sheaf.Paper.GabberCriterionDegree`, were read
whole: both have proof-only imports and no application to adapt. The text scan
of every transitive importer likewise finds no declaration use. No public
import changes. Thus every downstream statement and proof keeps its meaning;
no additional module requires editing. Groups below are the local claim snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | V1 | signature corrected; original proof remains open |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | B3 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | U1 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | P1 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | N1 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | A2 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | Q1 | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.Paper.GabberCriterion | unclaimed in local snapshot | direct proof import only; no theorem call; no adaptation |
| Sheaf.Paper.GabberCriterionDegree | unclaimed in local snapshot | direct proof import only; no theorem call; no adaptation |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| TargetsCheck | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | T2 | no declaration use; statements and proofs unchanged |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Defs | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Inversion | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Perverse | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Properties | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Gabber | Q2 | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed in local snapshot | no declaration use; statements and proofs unchanged |

## Status

landed 20261012T063524-L-3161736 2026-10-12 (merge of deliver/V1/Sheaf.Paper.StrictHenselianZariskiEtaleComparison)
