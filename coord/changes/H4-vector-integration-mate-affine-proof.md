# AlgebraicGeometry.Etale.vectorIntegrationMate_isIso

## Reason

The existing proof imports general SmoothDuality, whose closure was quarantined for the false SfP1ProjectionTraceFalseTail. The independently normalized bundle construction needed by this item uses this theorem. Replace its proof with the explicit affine adjunction and frame-descent argument on every unbounded complex. This module is unclaimed in the current shared snapshot. No definition or public interface changes. All original private helpers and instances are retained for `import all` consumers. The unused private tensor-counit import is removed. Two new proved private helpers handle the affine counit and right-functor normal form.

## Old

```lean
theorem vectorIntegrationMate_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    ∀ [IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
        (vectorIntegrationCoefficient A N hA S d M))],
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d M)).homEquiv _ K
        (inv (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
          (vectorIntegrationCoefficient A N hA S d M)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
            (vectorBundleIntegration N hN A hA S hS d M) ≫
              (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom))
```

Proof used the canonical smooth tensor mate to extend unit-level invertibility.

## New

```lean
theorem vectorIntegrationMate_isIso (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (M : SheafOfModules.{u} S.ringCatSheaf) [M.IsFiniteLocallyFreeOfRank d]
    (K : DerivedCategoryModule A S) :
    letI : IsAffineHom (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).1
    letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d M) :=
      (vectorIntegration_geometry S d M).2.1
    ∀ [IsIso (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
        (vectorIntegrationCoefficient A N hA S d M))],
    IsIso ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A)
      (VectorBundleZeroSection.π S d M)).homEquiv _ K
        (inv (compactProjectionMapCoeffFirst A (VectorBundleZeroSection.π S d M) K
          (vectorIntegrationCoefficient A N hA S d M)) ≫
          ((derivedTensor (ModuleCat.{u + 1} A) S).obj K).map
            (vectorBundleIntegration N hN A hA S hS d M) ≫
              (derivedTensorRightUnitor (ModuleCat.{u + 1} A) S K).hom))
```

Same statement, all existing helper signatures/instances, and public imports. Proof uses affineTraceLineCounit_isIso, affineTraceRight_normalForm, compact-support comparison, exceptional open base change, and conservative frame pullbacks. No sorry is introduced by this repair.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BundleSectionPurityUnitIsIso | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Paper.NormalizedVectorPurityBundle | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Paper.DiagonalOrientationChartExistence | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Paper.DiagonalOrientationCompatibility | unclaimed | Same interface; compatibility compile, no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | R1 | Same interface. Existing timeout: 64 s with repair, 66 s with original dependency; no adaptation. |

The first three rows are the external textual users of vectorIntegrationMate_isIso from tools/downstream.py --uses. The remaining rows are the additional direct importers, including `import all` users. Transitive users need no adaptation because signatures, instances, definitions, attributes and public imports are preserved.

## Status

landed 20261027T180636-L-3885298 2026-10-27 (merge of deliver/H4/Sheaf.Paper.NormalizedVectorPurityBaseChange)
