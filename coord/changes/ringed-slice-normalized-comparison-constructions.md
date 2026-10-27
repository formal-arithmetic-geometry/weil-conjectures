# CategoryTheory.ringedSlice_normalizedComparisons and its concrete comparison proofs

## Reason

The assignment names the archived D4 red-build repair, whose archive is now marked
resolved. The live K2 assembly already has zero textual holes. Its two comparison
construction dependencies each have one hole. This delivery completes both existing
obligations rather than reintroducing the archived monolithic proof. The concrete
ordinary tensor and Hom constructions are recovered from the archived D4 proof and
adapted to the current library with transparency checking enabled. A private generic
inverse-comparison lemma avoids rewriting through concrete Hom functor instances.
The item's comparison-data constructor is abstracted over its two categories so
its assembly does not unfold the chain comparison constructions.

The two dependency modules are unclaimed (no corresponding coord/claims filename).
They are permitted proof changes, not forced adaptations to another group's work.
No source-library file, public import, declaration signature, existing attribute,
instance, or public data definition is changed. All new helpers are private and
proved. The existing theorem docstrings are preserved verbatim. There is no change
to any target statement or its meaning, and no new target-definition review is needed.

## Old

Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons

```lean
theorem ringedSlice_normalizedComparisons
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U) (forget₂
      CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))]
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, u, w} J A))
    (T : CoefficientTensorModels.{u, c, v, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, max c v, v, w'} (J.over U) (A.over U) SU) :
    Nonempty {d : RingedSliceEvaluationComparisons (derivedInternalHomOfUniverses.{c, v, u, w} J A)
      (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U) S SU (RingedSliceFlatRestriction.{c, v,
      u} J A U) // RingedSliceEvaluationNormalized.{c, v, u, w, w'} J A U S T SU TU d}
```

Sheaf.Algebra.Homology.RingedSliceTotalTensorComparison

```lean
theorem ringedSlice_totalTensorComparison_exists (U : C) :
    ∃ γ : coefficientTotalTensor.{u, c, v} J A ⋙
        ringedSliceComplexRestriction.{c, v, u} J A U ≅
      ((ringedSliceComplexRestriction.{c, v, u} J A U).prod
        (ringedSliceComplexRestriction.{c, v, u} J A U)) ⋙
          coefficientTotalTensor.{u, max c v, v} (J.over U) (A.over U),
      ∀ (P Q : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂
        CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : Over U)
        (x : (P.X p).val.obj (op V.left)) (y : (Q.X q).val.obj (op V.left)),
        ((γ.hom.app (P, Q)).f k).val.app (op V)
          (coefficientTensorGenerator.{u, c, v} J A P Q p q k h (op V.left) x y) =
        coefficientTensorGenerator.{u, max c v, v} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj P)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj Q) p q k h (op V) x y
```

Sheaf.Algebra.Homology.RingedSliceHomComparisonExistence

```lean
theorem ringedSlice_homComparison_exists
    (U : C) [HasDerivedCategory.{w'} (SheafOfModules.{max c v u} ((sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj (A.over U)))] :
    ∃ η : derivedInternalHomOfUniverses.{c, v, u, w} J A ⋙
        ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U ≅
      ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).op.prod
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U)) ⋙
          derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U),
  ∀ (L I : CochainComplex (SheafOfModules.{max c v u} ((sheafCompose J (forget₂ CommRingCat.{max c v
      u} RingCat.{max c v u})).obj A)) ℤ) [I.IsKInjective],
      ∃ (κ : (derivedInternalHomOfUniverses.{c, v, u, w} J A).obj
            (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≅
            DerivedCategory.Q.obj (homComplex (R := A) L I))
        (κU : (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).obj
          (op (DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
            DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)) ≅
          DerivedCategory.Q.obj (homComplex (R := A.over U)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
        (γ : (ringedSliceComplexRestriction.{c, v, u} J A U).obj (homComplex (R := A) L I) ≅
          homComplex (R := A.over U) ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)),
        RingedKInjectiveHomModel.{c, v, u, w} J A L I κ ∧
        RingedKInjectiveHomModel.{max c v, v, u, w'} (J.over U) (A.over U)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
          ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) κU ∧
        (∀ (n p q : ℤ) (h : p + n = q) (V : Over U)
          (W : Over V) (x : (L.X p).val.obj (op W.left.left))
          (z : ((homComplex (R := A) L I).X n).val.obj (op V.left)),
          (((coefficientHomComponent.{u, max c v, v} (J.over U) (A.over U)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)
            ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I) n p q h).val.app (op V)
              ((γ.hom.f n).val.app (op V) z)).app (op W)).hom x =
          (((coefficientHomComponent.{u, c, v} J A L I n p q h).val.app (op V.left) z).app
            (op (Over.mk W.hom.left))).hom x) ∧
        (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).map κ.hom ≫
          (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app (homComplex (R := A) L I) ≫
          DerivedCategory.Q.map γ.hom =
        η.hom.app (op (DerivedCategory.Q.obj L), DerivedCategory.Q.obj I) ≫
          (derivedInternalHomOfUniverses.{max c v, v, u, w'} (J.over U) (A.over U)).map
            (X := (op ((ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
              (DerivedCategory.Q.obj L)), (ringedSliceDerivedRestriction.{c, v, u, w, w'} J A U).obj
              (DerivedCategory.Q.obj I)))
            (Y := (op (DerivedCategory.Q.obj
              ((ringedSliceComplexRestriction.{c, v, u} J A U).obj L)),
              DerivedCategory.Q.obj ((ringedSliceComplexRestriction.{c, v, u} J A U).obj I)))
            (((ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).inv.app L).op,
              (ringedSliceLocalizationIso.{c, v, u, w, w'} J A U).hom.app I) ≫ κU.hom
```

The first theorem already has a complete assembly proof. Each of the last two
proofs is `by sorry`.

## New

The three signatures above are byte-for-byte unchanged. The two formerly missing
proofs now construct their ordinary chain isomorphisms and representative equations.
Tensor restriction uses native tensor conjugation and total-bifunctor comparison.
Hom restriction uses product projections, fixed K-injective augmentation and descent.
The main theorem keeps the current K2 assembly and uses a new private generic
`comparisonData` constructor for its record literal. It continues to use the existing
proved Koszul comparison. There are no new public declarations or added hypotheses.

## Users

The direct importer and declaration-use scans were read against the current source.
The two construction theorems are used only by the item. The item has four direct
importers, three of which call its theorem. All use exactly the same public types.
The three old red-build failures are included as additional regression checks.
All seven checks passed without errors or warnings, each below 60 s. The unchanged
copies used only for compilation were verified equal to the shared source and
removed before delivery. No downstream source adaptation was necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons | B2 | Same theorem; generic private record construction. |
| Sheaf.Algebra.Homology.RingedSliceTotalTensorComparison | unclaimed | Existing theorem proved; same signature and public import. |
| Sheaf.Algebra.Homology.RingedSliceHomComparisonExistence | unclaimed | Existing theorem proved; same signature and public import. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose | unclaimed | Same comparison existence theorem and normalization data. |
| Sheaf.CategoryTheory.RingedSiteSignedDualRestriction | unclaimed | Same independently quantified derived universes and representative conditions. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Same application of normalized comparison existence. |
| Sheaf.AlgebraicGeometry.AlgebraicSpacePerfectObjectsCompact | unclaimed | Existing private import remains compatible; no direct theorem use. |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | Old repair regression; no source adaptation. |
| Sheaf.Paper.CompletedTowerDirectImage | unclaimed | Old repair regression; no source adaptation. |
| Sheaf.Paper.PerfectChartTensorComparison | unclaimed | Old repair regression; no source adaptation. |

## Status

landed 20261026T154307-L-1630540 2026-10-26 (merge of deliver/B2/Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons)
