# CategoryTheory.filteredStationary_cycle_comparison

## Reason

Complete the human-approved retirement listed in `coord/retire-items.tsv` by using
`WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison` in place of its
proved Sheaf copy. The theorem signatures are byte-identical. The API difference
reported for `filtered_class_preimage` concerns a private helper only; no consumer
uses it. The only source difference relevant to the proof route is the upstream
private `quotient_kernel` using the proved private kernel-pullback helper from
`WeilConjectures.CategoryTheory.DerivedCoupleKernelIdentities` instead of Mathlib's
`pullback_equalizer` directly. Preserve this dependency in the DAG.

## Old

Module: `Sheaf.CategoryTheory.FilteredStationaryCycleComparison`.

```lean
theorem filteredStationary_cycle_comparison
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K)
    (q p r : ℤ) (hr : 1 ≤ r)
    (hupper : F.complexStep (q + r) (q + p + 1) = ⊥)
    (hlower : F.complexStep (q - r + 1) (q + p - 1) = ⊤)
    {Y : C} (c : K.homology (q + p) ≅ Y) (H : DecreasingFiltration Y)
    (a : ∀ i : ℤ, (F.step i : CochainComplex C ℤ).homology (q + p) ⟶ (H.step i : C))
    (ha : ∀ i : ℤ, a i ≫ (H.step i).arrow =
      HomologicalComplex.homologyMap (F.step i).arrow (q + p) ≫ c.hom)
    (hepi : ∀ i : ℤ, Epi (a i)) :
    ∃ (z : (F.step q : CochainComplex C ℤ).cycles (q + p) ⟶
        (F.complexCycles q (q + p) r : C))
      (e : filteredComplexPageObject K F r (q, p) ≅ H.gradedPiece q),
      Epi z ∧
      z ≫ (F.complexCycles q (q + p) r).arrow =
        (F.step q : CochainComplex C ℤ).iCycles (q + p) ≫
          (F.complexQuotientπ q (q + 1) (by omega)).f (q + p) ∧
      z ≫ filteredComplexPageπ K F r (q, p) ≫ e.hom =
        (F.step q : CochainComplex C ℤ).homologyπ (q + p) ≫ a q ≫
          cokernel.π (Subobject.ofLE (H.step (q + 1)) (H.step q)
            (H.antitone_step (Int.le_add_one (le_refl q))))
```

## New

The identical signature above is supplied by the existing source module
`WeilConjectures.CategoryTheory.FilteredStationaryCycleComparison`. No upstream file
is changed. The Sheaf copy is withdrawn through `deleted.txt`, all three current
direct consumers change just their private import, and the node's Lean attachment
points to the upstream theorem. All statement and proof dependencies remain;
`lem-sp-derived-couple-kernel-identities` is added to reflect the actual upstream
proof helper. No new definition, statement, instance, axiom or hole is introduced.

## Users

The current direct-import scan finds three consumers, including
`FilteredPageTwoComparison`, absent from the older retirement row. The full reverse
import closure has the following 18 modules. No rework archive references the copy.
The group column records claims present in the shared snapshot.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.FilteredPageTwoComparison | unclaimed | Replace only the private import; all signatures and proofs unchanged. |
| Sheaf.Paper.EtaleCECoherentFirstPageLifts | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCECoherentPrescribedResolutions | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCECoherentQuotientPresentations | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCEFilteredTotalConstruction | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCEQuotientPageDescent | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds | unclaimed | Replace only the private import; all signatures and proofs unchanged. |
| Sheaf.Paper.EtaleCEStationaryPageNaturality | unclaimed | Replace only the private import; all signatures and proofs unchanged. |
| Sheaf.Paper.EtaleCESupportedFirstPageLifts | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologyCETotalMaps | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologyPullbackMaps | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologySupportedCETotals | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.EtaleHypercohomologySupportedResolutionMaps | unclaimed | No edit; receives the identical theorem through its dependencies. |
| Sheaf.Paper.FlatFilteredComplexComparison | unclaimed | No edit; receives the identical theorem through its dependencies. |

The supplied public theorem, its cycles and page objects, and its representative
and quotient equations are identical. Thus downstream mathematical statements do
not change. The unit `sk-prop-h2` and all DAG parent edges are preserved. The source
closure scan finds no nonempty pair of twins in the three consumer environments.

## Status

landed 20261021T002936-L-1581369 2026-10-21 (merge of deliver/J1/Sheaf.CategoryTheory.FilteredStationaryCycleComparison)
