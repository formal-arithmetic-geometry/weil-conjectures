# CategoryTheory.DecreasingFiltration.cohomologyImage

## Reason

The retirement inventory lists this zero-hole module because the adopted upstream module
already supplies the cohomology image filtration as `homologyFiltration` and proves the
same finiteness theorem. The original Sheaf module constructs the same filtration again
and duplicates the public theorem `cohomologyImage_isFinite`.

Use the canonical construction and theorem. Keep `cohomologyImage` as an abbreviation,
following the project's rule that a second name for a notion becomes an abbreviation of
the existing definition. This compatibility module is still needed by current consumers;
it is not withdrawn. Full withdrawal would require changing signatures of held consumers.
The previous full-withdrawal packet was refused for precisely those signature changes.
This packet removes the duplicated mathematical construction and finiteness proof from
the item itself. A newly landed, unclaimed consumer requires the proof-only adaptation
recorded below.

## Old

```lean
noncomputable def cohomologyImage (n : ℤ) : DecreasingFiltration (K.homology n) where
  F p := imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n)
  F_succ_le p := by
    let q := p + 1
    have hpq : p ≤ q := by dsimp [q]; omega
    have h := imageSubobject_comp_le
      (HomologicalComplex.homologyMap
        (Subobject.ofLE (L.step q) (L.step p) (L.antitone_step hpq)) n)
      (HomologicalComplex.homologyMap (L.step p).arrow n)
    simpa only [← HomologicalComplex.homologyMap_comp, Subobject.ofLE_arrow] using h

theorem cohomologyImage_isFinite
    (hfinite : ∀ n : ℤ, ∃ lo hi : ℤ,
      L.complexStep lo n = ⊤ ∧ L.complexStep hi n = ⊥)
    (n : ℤ) : (L.cohomologyImage n).IsFinite
```

The old theorem has the complete three-degree isomorphism and zero-term proof in this module.
Its private helper `complexStep_antitone` supports only that duplicated proof.

## New

```lean
public import WeilConjectures.CategoryTheory.FilteredCohomologyImage

noncomputable abbrev cohomologyImage (n : ℤ) : DecreasingFiltration (K.homology n) :=
  L.homologyFiltration n
```

The existing upstream `CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite`
has exactly the same binders and conclusion `(L.homologyFiltration n).IsFinite`.
This is definitionally equal to the original conclusion through the abbreviation.
The item no longer redeclares this theorem or its private antitonicity helper.
The DAG finiteness node attaches to that complete upstream theorem; its mathematical
statement, parents and proof dependencies remain intact.

An isolated compiled probe copies the entire original filtration under `originalImage`.
Both `originalImage = homologyFiltration` and the new `cohomologyImage = originalImage`
are proved by `rfl`, uniformly in the category, complex, filtration and degree.
The homology-filtration step is the original imageSubobject by `rfl`. Thus steps,
antitonicity proofs and graded pieces retain exactly their meaning, including for zero
complexes and arbitrary filtration bounds. The same probe applies the upstream finiteness
theorem at the old conclusion `(L.cohomologyImage n).IsFinite` without a cast.
No source-library declaration or target signature changes. The equality check establishes
that targets using this definition retain their mathematical meaning.

The newly available, unclaimed consumer
`Sheaf.CategoryTheory.FilteredPageTwoComparison` uses `dsimp only` to unfold the old
construction before rewriting image-subobject arrows in
`cohomology_restriction_naturality`. Against the abbreviation, its line 244 fails with
`Tactic rewrite failed: Did not find an occurrence of the pattern
factorThruImageSubobject ?f ≫ (imageSubobject ?f).arrow`.
The delivery replaces only that unfolding step (original line 243) by a `change` giving
the same image-subobject expression explicitly. The remaining proof, declarations,
signatures, imports and attributes are unchanged. This is a forced proof adaptation,
not a new mathematical statement. Its unchanged original and adapted version are both
compiled against this delivery to establish the need for the edit.

## Users

The following current downstream users were listed by `tools/downstream.py`; all their
public signatures remain unchanged. The five original direct consumers are validated
verbatim against the changed item, including those held by C4 and J1. The two immediate
paper callers are also validated verbatim.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence | unclaimed; quarantined | Archived source unchanged. Its cohomology_image_preserves lemma and abutment HF use cohomologyImage; its finiteness call uses cohomologyImage_isFinite. Both interfaces remain definitionally identical; no adaptation or restoration is part of this repair. |
| Sheaf.CategoryTheory.FilteredPageTwoComparison | unclaimed | One proof-only adaptation in cohomology_restriction_naturality: explicitly change the target to its image-subobject expression before rewriting. Original fails against the abbreviation; adapted source compiles. All signatures and finiteness calls unchanged. |
| Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap | C4 | Source unchanged; original compiles against the compatibility abbreviation. |
| Sheaf.CategoryTheory.FilteredCohomologyImageNormalized | unclaimed | Source unchanged; original compiles against the compatibility abbreviation. |
| Sheaf.CategoryTheory.FilteredCohomologyImagePresentation | unclaimed | Source unchanged; original compiles against the compatibility abbreviation. |
| Sheaf.CategoryTheory.FilteredStableSubquotient | unclaimed | Source unchanged; original compiles against the compatibility abbreviation. |
| Sheaf.CategoryTheory.FilteredStationaryCycleComparison | J1 | Source unchanged; original compiles against the compatibility abbreviation. |
| Sheaf.Paper.EtaleCECoherentFirstPageLifts | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCECoherentPrescribedResolutions | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCECoherentQuotientPresentations | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEFilteredTotalConstruction | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEPrescribedNormalizedFirstPages | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEPrescribedQuotientPageDescent | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEQuotientPageDescent | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCEStationaryPageNaturality | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleCESupportedFirstPageLifts | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologyCETotalMaps | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologyPullbackMaps | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologySupportedCETotals | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.Paper.EtaleHypercohomologySupportedResolutionMaps | unclaimed | Source unchanged; the two immediate stationary callers are compiled as probes. |
| Sheaf.CategoryTheory.FilteredCohomologyImage | C1 | Canonical abbreviation replaces duplicate construction; theorem comes from upstream. |

The quarantined Cartan--Eilenberg parent listed in the table is preserved at
`quarantine/Sheaf/CategoryTheory/CartanEilenbergComparisonIndependence.lean`, together
with its Lean attachment and DAG edges. Its original import of this compatibility module,
its `cohomologyImage` references, and its application of `cohomologyImage_isFinite`
need no migration. The unrelated stale interfaces in that archive remain the responsibility
of its restoration item. `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` has since
been restored and no longer imports this module or mentions either changed name.
No DAG node or unit step is bypassed. The finiteness node stays available to all its parents.

## Status

landed 20261021T001109-L-1370805 2026-10-21 (merge of deliver/C1/Sheaf.CategoryTheory.FilteredCohomologyImage)
