# AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_transport_kflat_derived

## Reason

The derived section comparison `barLam` was universally quantified but unrelated to the
normalized internal comparison `lam`. The conclusion is therefore false as stated:
negating `barLam` changes its left side without changing any hypothesis or its right side.
For identity coefficient and geometric maps over integer coefficients, evaluate on the
regular module in degree zero. The positive and negative automorphisms cannot both give
the same computation equation. This is a statement defect, not a new flatness assumption.

Add the missing conjugation/realization equation. The parent already defines `barLam`
by conjugation. Its private realization lemma proves the equation by `map_preimage`,
whiskering and cancellation of isomorphisms. The parent's public signatures and its
ordinary/derived normalization property are preserved. No target changes.

## Old

```lean
theorem section_pull_transport_kflat_derived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E)
    (he : ∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) :
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
```

## New

```lean
theorem section_pull_transport_kflat_derived {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅
      derivedPullback Λ f ⋙ cX.model.T)
    (hbarLam : ∀ M : DerivedCategory (Modules Λ Y),
      (derivedEquivalence Λ' X).functor.map (lam.hom.app M) ≫
          cX.derived.hom.app ((L Λ f).obj M) ≫
          cX.model.T.map ((scalarSectionPullComparison Λ f).hom.app M) =
        (scalarSectionPullComparison Λ' f).hom.app ((D a Y).obj M) ≫
          (derivedPullback Λ' f).map (cY.derived.hom.app M) ≫
          barLam.hom.app ((derivedEquivalence Λ Y).functor.obj M))
    (e : cY.model.E ⋙ pullback Λ' f ≅ pullback Λ f ⋙ cX.model.E)
    (he : ∀ M : Modules Λ Y,
      (equivalence Λ' X).functor.map ((CondensedRing.pullIso a f).inv.app M) ≫
          cX.ordinary.hom.app ((CondensedRing.upperStar Λ f).obj M) ≫
          cX.model.E.map ((pullComparison Λ f).hom.app M) =
        (pullComparison Λ' f).hom.app ((QuotientChange.extension a Y).obj M) ≫
          (pullback Λ' f).map (cY.ordinary.hom.app M) ≫
          e.hom.app ((equivalence Λ Y).functor.obj M)) :
    ∀ P : CochainComplex (modules Λ Y) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      barLam.hom.app (DerivedCategory.Q.obj P) ≫
          cX.model.T.map ((pullback Λ f).mapDerivedCategoryFactors.hom.app P) ≫
          cX.model.ε.app (((pullback Λ f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
            (Iso.refl (pullback Λ f ⋙ cX.model.E)) (.up ℤ)).hom.app P) =
        (derivedPullback Λ' f).map (cY.model.ε.app P) ≫
          (pullback Λ' f).mapDerivedCategoryFactors.hom.app
            ((cY.model.E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app P)
```

The added public import `Sheaf.Paper.InternalScalarPullbackNormalizationData` provides
the canonical `scalarSectionPullComparison` appearing in the new hypothesis. Other
new imports are proof imports; the prior private `IntegralResidueDerivedMonoidal`
import is replaced by the scoped existing-instance cache used in this calculation.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientSectionPullTransportKFlatDerived | E8 | Corrected theorem; complete proof of the representative equation. |
| Sheaf.Paper.QuotientSectionPullTransportKFlat | unclaimed in the shared snapshot | Forced caller adaptation: prove the conjugation equation and pass it to the corrected theorem; all existing signatures and imports stay identical. |

The textual `tools/downstream.py --uses` search found exactly these two occurrences
(including the declaration itself). There is one direct importer of the changed item,
`Sheaf.Paper.QuotientSectionPullTransportKFlat`. Its direct importers are
`Sheaf.Paper.QuotientSectionPullTransportLocalization` and
`Sheaf.Paper.QuotientSectionPullTransportExtension`; both are checked against the delivery.
No indirect user mentions the corrected declaration.

## Status

landed 20261028T020332-L-2496671 2026-10-28 (merge of deliver/E8/Sheaf.Paper.QuotientSectionPullTransportKFlatDerived)
