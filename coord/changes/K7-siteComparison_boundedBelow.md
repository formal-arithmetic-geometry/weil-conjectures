# AlgebraicGeometry.ProEtale.siteComparison_boundedBelow

## Reason

Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived was unclaimed when edited. This is a dependency used by the assigned comparison
proof. The required finite-level comparison theorem supplies the ordinary unit and injective acyclicity to prove the bounded-below derived unit. Compose its fully faithful left functor with exact coefficient realization, using the canonical composition isomorphism. Full faithfulness makes the unit of the specified transported adjunction invertible. Only proof imports are added; signatures and visibility stay identical.

## Old

```lean
theorem siteComparison_boundedBelow (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit
```

The proof was `by sorry`.

## New

```lean
theorem siteComparison_boundedBelow (T : Scheme.{u}) (Λ : Type (u + 1))
    [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    Nonempty (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.FullyFaithful ∧
      IsIso (finiteCoefficientDerivedComparisonAdjunction T Λ).unit := by
  let L := comparisonUpperStar (ModuleCat.{u + 1} Λ) T
  let E := finiteCoefficientRealization T Λ
  let adj := comparisonAdjunction (ModuleCat.{u + 1} Λ) T
  obtain ⟨_, _, hunit, hacyclic⟩ := siteComparison_finiteLevel T Λ
  have hu : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ hunit I)
      (fun I _ n ↦ hacyclic I inferInstance (n + 1) (Nat.succ_pos n)) K
  let fL := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  let fE := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι ⋙ E.mapDerivedCategory)).ofIso
      E.mapDerivedCategoryPlusCompatibility.symm
  let e := Functor.mapDerivedCategoryPlusCompIso L E
  let ff := fL.comp (Functor.FullyFaithful.ofCompFaithful fE)
  let f := ff.ofIso e.symm
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Full := f.full
  have : (finiteCoefficientComparison T Λ).mapDerivedCategoryPlus.Faithful := f.faithful
  exact ⟨⟨f⟩, inferInstance⟩
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized | F1 | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleStalkConservative | H1 | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.CoefficientSystemDerivedComparison | Q2 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.IntegralStratifiedPerfectCharacterization | Z6 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | M7 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.NormalizedEtaleOriginWitnesses | A8 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.PbcUniformCompleteTriangulated | Q5 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.PreservationConstructible | B5 | Same signature and visibility; no adaptation. |
| Sheaf.Paper.PurityComparisonUnitInjectiveModel | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Same signature and visibility; no adaptation. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | unclaimed | Same signature and visibility; no adaptation. |

All public signatures and public imports are identical. No definition or target changes.
No forced adaptation is included.

## Status

landed 20261019T005336-L-2754480 2026-10-19 (merge of deliver/K7/Sheaf.AlgebraicGeometry.UnboundedSiteComparison)
