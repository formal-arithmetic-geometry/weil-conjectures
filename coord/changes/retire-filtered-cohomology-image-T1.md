# Retire the duplicate cohomology image filtration (T1)

## Reason

`Sheaf.CategoryTheory.FilteredCohomologyImage` is the depth-2 retirement item in
`coord/retire-items.tsv`, under the human's 2026-10-20 retirement instruction.
Its upstream twin has the same finiteness theorem, expressed using the existing
`CategoryTheory.DecreasingFiltration.homologyFiltration`. The copy's
`cohomologyImage` duplicates that construction. Migrate all remaining references
and withdraw the copy, preserving every proved consumer and the unit route.

## Old

The copy defines

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
```

It proves `CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite` with conclusion
`(L.cohomologyImage n).IsFinite`. Consumers refer to the steps and graded pieces of
this duplicate construction. There are zero holes in the item and its five adapted consumers.

## New

Withdraw `lean/Sheaf/CategoryTheory/FilteredCohomologyImage.lean` with `deleted.txt`.
Every direct importer instead imports
`WeilConjectures.CategoryTheory.FilteredCohomologyImage` with the original import visibility.
Replace references to the filtration `L.cohomologyImage n` by `L.homologyFiltration n`.
Keep the consumer theorem names and their proofs, with these necessary name replacements.

The replacement is the existing definition in
`WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex`:

```lean
noncomputable def homologyFiltration (n : ℤ) : DecreasingFiltration (K.homology n) :=
  F.exactCouple.abutmentFiltration F.toHomology F.α_toHomology n
```

`ExactCouple.abutmentFiltration` takes the images of `toHomology`; the latter is
`HomologicalComplex.homologyMap (F.F p).arrow n`. Thus both filtrations have definitionally
equal fields of subobjects; the antitonicity proofs agree by proof irrelevance.
A separate compiled check copies the entire original definition under `originalImage`
and proves `L.originalImage n = L.homologyFiltration n` by `rfl`, without extra hypotheses.
It also verifies the replacement's step formula by `rfl`.
This applies to every abelian category and complex, including zero complexes and arbitrary
filtration bounds. Steps, inclusions, and graded pieces retain exactly their meaning.

The upstream finiteness theorem retains the name
`CategoryTheory.DecreasingFiltration.cohomologyImage_isFinite`, the same binders, and conclusion
`(L.homologyFiltration n).IsFinite`. The node
`lem-sp-filtered-cohomology-image-finite` now records this upstream theorem and notes the
location of the existing filtration definition. Four consumer node Lean statement strings
use `homologyFiltration`; their mathematical statements and all dependencies stay intact.
One proof-step description names the replacement filtration. No new node or theorem is added.
No upstream source or target statement changes. Targets using this filtration remain subject
to the ordinary independent definition review; the compiled definitional equality verifies
that the replacement does not change their mathematical meaning.

## Users

All five adapted modules are unclaimed when inspected. The two further consumers are
copied verbatim for validation only; they do not appear in the delivery diff.

| Module | Holder | Effect |
|---|---|---|
| Sheaf.CategoryTheory.FilteredCohomologyImage | T1 | Withdraw duplicate; use upstream finiteness theorem. |
| Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap | unclaimed | Replace public import and filtration references in its public theorem and private proof lemmas. |
| Sheaf.CategoryTheory.FilteredCohomologyImageNormalized | unclaimed | Replace public import and filtration references in statement and proof. |
| Sheaf.CategoryTheory.FilteredCohomologyImagePresentation | unclaimed | Replace public import and filtration reference in statement. |
| Sheaf.CategoryTheory.FilteredStableSubquotient | unclaimed | Replace public import and filtration reference in statement. |
| Sheaf.CategoryTheory.FilteredStationaryCycleComparison | unclaimed | Replace private import and filtration references only in private lemmas/proofs; public signature identical. |
| Sheaf.Paper.EtaleCEStationaryComparisonsAtBounds | unchanged | Uses stationary comparison with its identical public signature. |
| Sheaf.Paper.EtaleCEStationaryPageNaturality | unchanged | Uses stationary comparison with its identical public signature. |

`tools/downstream.py` finds exactly these seven downstream modules; a source-wide search
finds no other uses of the duplicate definition. The retirement row's archived consumers
`Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence` and
`Sheaf.CategoryTheory.FilteredHomotopySpectralSequence` are already absent from the library;
these are preserved rework archives, not unused mathematics. The exact archives are
`quarantine/Sheaf/CategoryTheory/CartanEilenbergComparisonIndependence.lean` and
`quarantine/Sheaf/CategoryTheory/FilteredHomotopySpectralSequence.lean`, both recorded in
`coord/rework.tsv`. Their rework still needs these results: replace their import of the retired
copy by its upstream twin, every `.cohomologyImage n` by `.homologyFiltration n`, and the
qualified `DecreasingFiltration.cohomologyImage F n` form by
`DecreasingFiltration.homologyFiltration F n` (and likewise for G). The compiled universal
definitional equality justifies these replacements too. This packet neither restores the
archives' unrelated missing dependencies nor deletes or empties either archive, and it
preserves their Lean attachments and mathematical DAG dependencies. The existing parent
`lem-sp-cartan-eilenberg-comparison-independence` still uses the same finiteness node, now
attached to the upstream theorem; there is no withdrawal or bypass of that mathematical node.
All current importers of the withdrawn module are migrated in this packet. An import-closure
scan of each adapted module finds no environment containing both nonempty Sheaf and upstream
twins. The mathematical DAG node remains available to its existing parents through its
upstream attachment, so no parent dependency or blueprint unit step is bypassed.

## Status

landed 20261020T211827-L-3507818 2026-10-20 (merge of deliver/T1/Sheaf.CategoryTheory.FilteredCohomologyImage)
equality check. The delivery tool checks the packet, axioms, imports, and current consumers;
the maintainer independently reviews and globally builds the landing.
