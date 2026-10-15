# CategoryTheory.Adjunction.liftedCommGrpBranch

## Reason

Upstream review #1424 identified this theorem as a duplicate wrapper around Mathlib's
`Functor.mapCommGrp` and `Adjunction.mapCommGrp`. The duplicate module is withdrawn and its
caller is re-pointed to the existing declarations.

## Old

```lean
theorem liftedCommGrpBranch
    {A : Type uA} [Category.{vA} A] [CartesianMonoidalCategory A]
    {B : Type uB} [Category.{vB} B] [CartesianMonoidalCategory B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [PreservesFiniteProducts L]
    [PreservesFiniteProducts R] :
    let : BraidedCategory A := BraidedCategory.ofCartesianMonoidalCategory
    let : BraidedCategory B := BraidedCategory.ofCartesianMonoidalCategory
    (∃ (LF : CommGrp A ⥤ CommGrp B) (RF : CommGrp B ⥤ CommGrp A)
          (hL : LF ⋙ CommGrp.forget B = CommGrp.forget A ⋙ L)
          (hR : RF ⋙ CommGrp.forget A = CommGrp.forget B ⋙ R),
        let eL := eqToIso hL
        let eR := eqToIso hR
        ∃ (a : LF ⊣ RF),
          (∀ X : CommGrp A,
            MonObj.mul (X := (LF.obj X).X) ≫ eL.hom.app X =
              (eL.hom.app X ⊗ₘ eL.hom.app X) ≫
                (prodComparisonIso L X.X X.X).inv ≫ L.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (LF.obj X).X) ≫ eL.hom.app X =
              (preservesTerminalIso L).inv ≫ L.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (LF.obj X).X) ≫ eL.hom.app X =
              eL.hom.app X ≫ L.map (GrpObj.inv (X := X.X))) ∧
          (∀ X : CommGrp B,
            MonObj.mul (X := (RF.obj X).X) ≫ eR.hom.app X =
              (eR.hom.app X ⊗ₘ eR.hom.app X) ≫
                (prodComparisonIso R X.X X.X).inv ≫ R.map (MonObj.mul (X := X.X)) ∧
            MonObj.one (X := (RF.obj X).X) ≫ eR.hom.app X =
              (preservesTerminalIso R).inv ≫ R.map (MonObj.one (X := X.X)) ∧
            GrpObj.inv (X := (RF.obj X).X) ≫ eR.hom.app X =
              eR.hom.app X ≫ R.map (GrpObj.inv (X := X.X))) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (f : LF.obj X ⟶ Y),
            (CommGrp.forget A).map (a.homEquiv X Y f) ≫ eR.hom.app Y =
              adj.homEquiv X.X Y.X (eL.inv.app X ≫ (CommGrp.forget B).map f)) ∧
          (∀ X : CommGrp A,
            (CommGrp.forget A).map (a.unit.app X) ≫ eR.hom.app (LF.obj X) ≫
                R.map (eL.hom.app X) = adj.unit.app X.X) ∧
          (∀ Y : CommGrp B,
            L.map (eR.inv.app Y) ≫ eL.inv.app (RF.obj Y) ≫
                (CommGrp.forget B).map (a.counit.app Y) = adj.counit.app Y.X) ∧
          (∀ (X : CommGrp A) (Y : CommGrp B) (α : L.obj X.X ⟶ Y.X),
            (∃ f : LF.obj X ⟶ Y, eL.inv.app X ≫ (CommGrp.forget B).map f = α) ↔
              ∃ g : X ⟶ RF.obj Y,
                (CommGrp.forget A).map g ≫ eR.hom.app Y = adj.homEquiv X.X Y.X α))
```

## New

The duplicate declaration and module are removed. `LiftsGroupRingObjects` directly constructs
`L.mapCommGrp`, `R.mapCommGrp`, and `adj.mapCommGrp`, proving the same formulas inline.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch | C1 | Withdraw the duplicate wrapper (the claimed repair item). |
| Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ComparisonDirectImage | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianStratumDetection | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleBoundedBelowCoproducts | C2 | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonSections | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleComparisonStalk | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleFunctionsQuotientSections | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImage | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOperations | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparison | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects | unclaimed | Forced adaptation: replace the withdrawn call with the direct Mathlib construction; signature unchanged. |
| Sheaf.CategoryTheory.ModulePullbackTensorIso | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.AdicLisseModule | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.FiniteCtfTriangulated | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.FiniteRingConstructibleSheafOrigin | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.FiniteTorsionConstructibility | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProEtaleConstructibleSheaf | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProEtaleLisseOrigin | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProEtaleResidueTorTest | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProfinitePointPullback | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProjectionFormulaArrows | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProjectionFormulaFiniteFree | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProjectionFormulaProjectiveSummand | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.ProjectionFormulaTotalization | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.RingedExchangeTensorCoherence | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.RingedTensorSquarePresentation | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.Paper.RingedTopoiCanonicalTensorPullback | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| TargetsCheck | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No source change: no use of the retired name; caller signature and public imports unchanged. |
| Sheaf.CategoryTheory.SitePullbackAbelianUnderlying | unclaimed | Documentation reference only; proof already uses Mathlib directly; no source change. |

`tools/downstream.py ... --uses liftedCommGrpBranch` reports only the retired declaration
and `LiftsGroupRingObjects` as code users. There are 69 transitive importers, which retain
the unchanged public caller interface. No target statement or definition changes.

The counterfactual original caller fails at old line 148 with
`error(lean.unknownIdentifier): Unknown identifier liftedCommGrpBranch` when compiled
against the withdrawn empty module. The adapted caller compiles. Only its obsolete
proof import and the proof body at that call changed. The public signature is unchanged.

## Status

landed 20261015T154155-L-159406 2026-10-15 (merge of deliver/C1/Sheaf.CategoryTheory.Adjunction.LiftedCommGrpBranch)
