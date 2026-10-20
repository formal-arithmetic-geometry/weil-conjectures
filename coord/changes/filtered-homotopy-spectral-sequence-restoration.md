# CategoryTheory.filteredHomotopy_spectralSequence_map_eq

## Reason

Restore the assigned quarantined module listed in coord/rework.tsv. The archive
imports the retired Sheaf filtration implementation and uses its old
FilteredObject.HomPreservingSteps name. The current canonical upstream API uses
FilteredObject.Hom with the same underlying map and step-preservation predicate.
Remove the obsolete import and use that current type throughout all three
restored signatures. The upstream canonical filtration is already publicly
imported by FilteredComplexSubquotients. No filtration definition is changed.

Complete the remaining page-map proof and remove unused proof imports. The
boundedness binders remain verbatim; the proof works from the supplied page
model without using them. A declaration-local unused-variable linter setting
records this fact. No target signature or adopted source file is changed.

## Old

The archived public import was:

```lean
public import Sheaf.CategoryTheory.Filtration
```

The three archived theorem signatures were:

```lean
theorem filteredHomotopy_page_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    ∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b

theorem exists_filteredHomology_map
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (n : ℤ) (AF : DecreasingFiltration (K.homology n))
    (BF : DecreasingFiltration (L.homology n))
    (hAF : ∀ p : ℤ, AF.step p = imageSubobject
      (HomologicalComplex.homologyMap (F.step p).arrow n))
    (hBF : ∀ p : ℤ, BF.step p = imageSubobject
      (HomologicalComplex.homologyMap (G.step p).arrow n)) :
    ∃ t : FilteredObject.HomPreservingSteps ⟨K.homology n, AF⟩
        ⟨L.homology n, BF⟩,
      t.hom = HomologicalComplex.homologyMap a.hom n ∧
      t.hom = HomologicalComplex.homologyMap b.hom n ∧
      ∀ p : ℤ, ∃ lift : (AF.step p : C) ⟶ (BF.step p : C),
        lift ≫ (BF.step p).arrow = (AF.step p).arrow ≫ t.hom

theorem filteredHomotopy_spectralSequence_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.HomPreservingSteps ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    (∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b) ∧
    (∀ (n : ℤ) (AF : DecreasingFiltration (K.homology n))
      (BF : DecreasingFiltration (L.homology n)),
      (∀ p : ℤ, AF.step p = imageSubobject
        (HomologicalComplex.homologyMap (F.step p).arrow n)) →
      (∀ p : ℤ, BF.step p = imageSubobject
        (HomologicalComplex.homologyMap (G.step p).arrow n)) →
      ∃ t : FilteredObject.HomPreservingSteps ⟨K.homology n, AF⟩ ⟨L.homology n, BF⟩,
        t.hom = HomologicalComplex.homologyMap a.hom n ∧
        t.hom = HomologicalComplex.homologyMap b.hom n ∧
        ∀ p : ℤ, ∃ g : AF.gradedPiece p ⟶ BF.gradedPiece p,
          cokernel.π (Subobject.ofLE (AF.step (p + 1)) (AF.step p)
            (AF.antitone_step (by omega))) ≫ g =
          Classical.choose (t.preserves p) ≫
            cokernel.π (Subobject.ofLE (BF.step (p + 1)) (BF.step p)
              (BF.antitone_step (by omega))))
```

## New

Remove the retired filtration import. Keep the existing public imports of
WeilConjectures.Algebra.Homology.FilteredComplexSubquotients,
Sheaf.CategoryTheory.FilteredPageTwoModel and Mathlib.Algebra.Homology.Homotopy.
The restored signatures use the canonical Hom type:

```lean
theorem filteredHomotopy_page_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    ∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b

theorem exists_filteredHomology_map
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (n : ℤ) (AF : DecreasingFiltration (K.homology n))
    (BF : DecreasingFiltration (L.homology n))
    (hAF : ∀ p : ℤ, AF.step p = imageSubobject
      (HomologicalComplex.homologyMap (F.step p).arrow n))
    (hBF : ∀ p : ℤ, BF.step p = imageSubobject
      (HomologicalComplex.homologyMap (G.step p).arrow n)) :
    ∃ t : FilteredObject.Hom ⟨K.homology n, AF⟩
        ⟨L.homology n, BF⟩,
      t.hom = HomologicalComplex.homologyMap a.hom n ∧
      t.hom = HomologicalComplex.homologyMap b.hom n ∧
      ∀ p : ℤ, ∃ lift : (AF.step p : C) ⟶ (BF.step p : C),
        lift ≫ (BF.step p).arrow = (AF.step p).arrow ≫ t.hom

theorem filteredHomotopy_spectralSequence_map_eq
    (K L : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (G : DecreasingFiltration L)
    (hKF : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      F.complexStep pmin n = ⊤ ∧ F.complexStep pmax n = ⊥)
    (hLG : ∀ n : ℤ, ∃ pmin : ℤ, ∃ pmax : ℤ,
      G.complexStep pmin n = ⊤ ∧ G.complexStep pmax n = ⊥)
    (a b : FilteredObject.Hom ⟨K, F⟩ ⟨L, G⟩)
    (H : Homotopy a.hom b.hom)
    (hshift : ∀ (p n : ℤ), ∃ ℓ :
      (F.complexStep p n : C) ⟶ (G.complexStep (p - 1) (n - 1) : C),
      ℓ ≫ (G.complexStep (p - 1) (n - 1)).arrow =
        (F.complexStep p n).arrow ≫ H.hom n (n - 1)) :
    (∀ (M : FilteredPageTwoModel C), M.S.map a = M.S.map b) ∧
    (∀ (n : ℤ) (AF : DecreasingFiltration (K.homology n))
      (BF : DecreasingFiltration (L.homology n)),
      (∀ p : ℤ, AF.step p = imageSubobject
        (HomologicalComplex.homologyMap (F.step p).arrow n)) →
      (∀ p : ℤ, BF.step p = imageSubobject
        (HomologicalComplex.homologyMap (G.step p).arrow n)) →
      ∃ t : FilteredObject.Hom ⟨K.homology n, AF⟩ ⟨L.homology n, BF⟩,
        t.hom = HomologicalComplex.homologyMap a.hom n ∧
        t.hom = HomologicalComplex.homologyMap b.hom n ∧
        ∀ p : ℤ, ∃ g : AF.gradedPiece p ⟶ BF.gradedPiece p,
          cokernel.π (Subobject.ofLE (AF.step (p + 1)) (AF.step p)
            (AF.antitone_step (by omega))) ≫ g =
          Classical.choose (t.preserves p) ≫
            cokernel.π (Subobject.ofLE (BF.step (p + 1)) (BF.step p)
              (BF.antitone_step (by omega))))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.FilteredHomotopySpectralSequence | C3 | Restored and proved; all three signatures preserve the mathematical statement. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence (quarantined) | unclaimed at inspection | The only archived direct importer and theorem user. Its positional invocation passes category morphisms, which are the current Hom type. The invocation needs no change; the archive has independent stale filtration imports and HomPreservingSteps references, outside this repair. Its dependency and attachment are preserved. |

No live Lean module imports or mentions the three declarations. The downstream
source tool is run with --allow-missing because the assigned module is currently
quarantined. The sole archived importer was also checked textually. No forced
consumer adaptation is necessary: restoration adds the formerly absent module,
and does not invalidate any currently compiling consumer.

## Status

landed 20261020T221104-L-4142321 2026-10-20 (merge of deliver/C3/Sheaf.CategoryTheory.FilteredHomotopySpectralSequence)
