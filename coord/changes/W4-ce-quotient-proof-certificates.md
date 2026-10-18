# AlgebraicGeometry.Etale.exists_etaleCE_coherent_quotient_presentations

## Reason

Replace the two embedded arithmetic proofs of `q ≤ q + 1` by explicit
`Int.le_add_one (le_refl q)` certificates. Profiling the original `by omega`
certificates showed repeated symbolic typeclass inference and arithmetic work.
This changes proof terms only: Lean proof irrelevance makes the old and new
declaration types definitionally equal. Every binder name, universe, hypothesis
and conclusion is retained. The theorem is not a Challenge target.

The file also applies **local** irreducibility attributes to CE row-comparison
and quotient definitions, so this proof uses their equations. These attributes
end with the namespace, do not change the definitions, and are not exported.
The static checker reports the attribute commands conservatively as an interface
change. No target meaning or existing public import changes. The new private
helpers are fully proved and do not occur in any public signature or data
definition.

## Old

```lean
theorem exists_etaleCE_coherent_quotient_presentations :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        FilteredComplexQuotientCoherence (P X K).sectionsTotal (P X K).L
          (P X K).sequence (e X K)) ∧
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      ∀ (p : ℕ) (q : ℤ)
        (m : (D.sequence.page 1).X (q, (p : ℤ)) ⟶
          (D'.sequence.page 1).X (q, (p : ℤ))),
        (∀ (A : AddCommGrpCat.{uNatural + 1})
          (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
          (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
          x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
            y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
          z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            x ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
          z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            y ≫ (D'.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) →
          z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
              (e X K q (p : ℤ) 1 (by decide)).inv ≫ m =
            z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv) →
        m ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))
```

## New

```lean
theorem exists_etaleCE_coherent_quotient_presentations :
    ∃ (P : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleTermwiseHypercohomology X K)
      (e : ∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        EtaleCEQuotientRealization (P X K)),
      (∀ (X : Scheme.{uNatural})
        (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})),
        FilteredComplexQuotientCoherence (P X K).sectionsTotal (P X K).L
          (P X K).sequence (e X K)) ∧
      ∀ {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (L : CochainComplex.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))
    (v : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K.obj ⟶ L.obj),
      let D := P X K
      let D' := P Y L
      ∀ (φ : (((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).mapHomologicalComplex (ComplexShape.up ℤ)).obj D.I ⟶ D'.I)
    (hφ : ∀ q : ℤ,
      (upperStar AddCommGrpCat.{uNatural + 1} f).map
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (K.obj.X q)).inv ≫
            (D.a.f q).f 0) ≫ (φ.f q).f 0 =
        v.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (L.obj.X q)).inv ≫
            (D'.a.f q).f 0)
    (u : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj D.sheafTotal ⟶ D'.sheafTotal)
    (hu : ∀ (m : ℕ) (q n : ℤ) (h : (m : ℤ) + q = n),
        (upperStar AddCommGrpCat.{uNatural + 1} f).map
            ((HomologicalComplex.extendXIso
              (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h) ≫ u.f n =
          (φ.f q).f m ≫
            (HomologicalComplex.extendXIso
              (((𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj (D'.I.X q))
              ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
                (((CartanEilenbergPresentation.mappedFunctor
                  (𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}))).obj
                    D'.I).flip).ιTotal (ComplexShape.up ℤ) (m : ℤ) q n h),
      let b := D.totalSectionsIso.hom ≫ ceSectionsLift f u ≫ D'.totalSectionsIso.inv
      ∀ (p : ℕ) (q : ℤ)
        (m : (D.sequence.page 1).X (q, (p : ℤ)) ⟶
          (D'.sequence.page 1).X (q, (p : ℤ))),
        (∀ (A : AddCommGrpCat.{uNatural + 1})
          (x : A ⟶ (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (y : A ⟶ (D'.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X
            (q + (p : ℤ)))
          (z : A ⟶ (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}))
          (z' : A ⟶ (D'.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1})),
          x ≫ (D.L.step q).arrow.f (q + (p : ℤ)) ≫ b.f (q + (p : ℤ)) =
            y ≫ (D'.L.step q).arrow.f (q + (p : ℤ)) →
          z ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            x ≫ (D.L.complexQuotientπ q (q + 1) (Int.le_add_one (le_refl q))).f (q + (p : ℤ)) →
          z' ≫ (D'.L.complexCycles q (q + (p : ℤ)) 1).arrow =
            y ≫ (D'.L.complexQuotientπ q (q + 1) (Int.le_add_one (le_refl q))).f (q + (p : ℤ)) →
          z ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
              (e X K q (p : ℤ) 1 (by decide)).inv ≫ m =
            z' ≫ filteredComplexPageπ D'.sectionsTotal D'.L 1 (q, (p : ℤ)) ≫
              (e Y L q (p : ℤ) 1 (by decide)).inv) →
        m ≫ (D'.firstPageIso p q).hom =
          (D.firstPageIso p q).hom ≫
            AddCommGrpCat.ofHom ((Sheaf.H.map (v.f q) p).comp
              (cohomologyMap f (K.obj.X q) p))
```

## Users

The downstream list and the direct declaration uses were read with
`tools/downstream.py --uses exists_etaleCE_coherent_quotient_presentations`.
No consumer needs adaptation: existing calls check at the same definitionally
equal type. In particular no module held by another group is modified.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleCECoherentQuotientPresentations | W4 | Item proof completed; type definitionally unchanged. |
| Sheaf.Paper.EtaleCECoherentFirstPageLifts | unclaimed | Transitive importer; no signature, definition or public-import change. |
| Sheaf.Paper.EtaleCEFilteredTotalConstruction | unclaimed | Transitive importer; no signature, definition or public-import change. |
| Sheaf.Paper.EtaleCEQuotientPageDescent | unclaimed | Direct declaration user; no adaptation, because only proof certificates change. |
| Sheaf.Paper.EtaleHypercohomologyCETotalMaps | unclaimed | Transitive importer; no signature, definition or public-import change. |
| Sheaf.Paper.EtaleHypercohomologyFilteredResolutionMaps | unclaimed | Transitive importer; no signature, definition or public-import change. |
| Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial | unclaimed | Transitive importer; no signature, definition or public-import change. |
| Sheaf.Paper.EtaleHypercohomologyPullbackMaps | unclaimed | Transitive importer; no signature, definition or public-import change. |

## Status

landed 20261018T071239-L-1682768 2026-10-18 (merge of deliver/W4/Sheaf.Paper.EtaleCECoherentQuotientPresentations)
