# ExteriorAlgebra.koszul_roof_comparison_independent

## Reason

The assigned retirement row in coord/retire-items.tsv preserves this Sheaf twin only
because the source theorem has a different signature. Inspection shows that the sole
difference is the unused hypothesis hregg: regularity of the second sequence. The source
module already contains the full proof of the same conclusion with all other hypotheses,
including both normalized augmentations, their quasi-isomorphisms, determinant comparison
normalizations and equality of derived roofs. Reuse that theorem and retire the duplicate.
No declaration, signature, attribute, import or body in WeilConjectures is changed.

## Old

In Sheaf.RingTheory.KoszulRoofComparisonIndependence:

```lean
theorem koszul_roof_comparison_independent
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hregg : RingTheory.Sequence.IsKoszulRegular g)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (ψ : koszulDualComplex A r g ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ)
    (hψ : IsKoszulConormalComparison A I r g hg ψ)
    (εf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (εg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    [QuasiIso εf] [QuasiIso εg]
    (haugf : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εf.f 0 (((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (haugg : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εg.f 0 (((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (zf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (zg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (heq : inv (DerivedCategory.Q.map εf) ≫ DerivedCategory.Q.map zf ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A) =
      inv (DerivedCategory.Q.map εg) ≫ DerivedCategory.Q.map zg ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A)) :
    koszulComparisonValue A I r f φ ((((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zf.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) =
      koszulComparisonValue A I r g ψ ((((koszulComplex A r g).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom))
```

The direct consumer imported Sheaf.RingTheory.KoszulRoofComparisonIndependence and called:

```lean
  have htransport := koszul_roof_comparison_independent A I r f₀ f hreg₀ hreg hf₀ hf
```

## New

The Sheaf module is withdrawn through deleted.txt. The DAG node remains attached to the
existing source theorem, whose signature is:

```lean
theorem koszul_roof_comparison_independent
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (I : Ideal A) (r : ℕ) (f g : Fin r → A)
    (hregf : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I)
    (φ : koszulDualComplex A r f ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (ψ : koszulDualComplex A r g ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) r).obj
        (koszulNormalDeterminant A I r))
    (hφ : IsKoszulConormalComparison A I r f hf φ)
    (hψ : IsKoszulConormalComparison A I r g hg ψ)
    (εf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    (εg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
    [QuasiIso εf] [QuasiIso εg]
    (haugf : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εf.f 0 (((koszulComplex A r f).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (haugg : ∀ x : ⋀[A]^0 (Fin r →₀ A),
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A (A ⧸ I))).hom
        (εg.f 0 (((koszulComplex A r g).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
      Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x))
    (zf : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (zg : (koszulComplex A r g).extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
    (heq : inv (DerivedCategory.Q.map εf) ≫ DerivedCategory.Q.map zf ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A) =
      inv (DerivedCategory.Q.map εg) ≫ DerivedCategory.Q.map zg ≫
        ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
          (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app (ModuleCat.of A A)) :
    koszulComparisonValue A I r f φ ((((koszulComplex A r f).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zf.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom)) =
      koszulComparisonValue A I r g ψ ((((koszulComplex A r g).extendXIso
      ComplexShape.embeddingDownNat (i := r) rfl).inv ≫ zg.f (-(r : ℤ)) ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
          (ModuleCat.of A A)).hom))
```

The direct consumer imports WeilConjectures.RingTheory.KoszulRoofComparisonIndependence and
uses the same theorem with the unused argument omitted:

```lean
  have htransport := koszul_roof_comparison_independent A I r f₀ f hreg₀ hf₀ hf
```

No surviving consumer declaration changes its signature or meaning. The parent DAG node
lem-sc-koszul-ext-determinant-roof retains its dependency on
lem-sc-koszul-roof-comparison-independence: this is a source-location migration, not a
withdrawal of the mathematical result or a bypass of the unit route. All proof dependencies
of the migrated node remain needed by the source proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulRoofComparisonIndependence | J9, assigned retirement | Withdrawn duplicate; theorem retained upstream. |
| Sheaf.RingTheory.KoszulRegularSequenceDualComplex | unclaimed in current local records | Private proof import migrated and unused hreg argument omitted; no signature change. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | not adapted | Transitive consumer; unchanged exported interface. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | not adapted | Transitive consumer; unchanged exported interface. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | not adapted | Transitive consumer; unchanged exported interface. |

Only the first consumer directly imported the retired module or applied its theorem.
The users were checked with tools/downstream.py --uses and a full source search. DAG
parents, including any archived parents, continue to use the same retained node id.
A sandbox test proves the entire former signature directly from the source theorem;
its axiom audit reports only propext, Classical.choice and Quot.sound. This test includes
the former second-regularity hypothesis, and does not specialize r or the quotient ring.
Thus r=0, I=A and all original edge cases remain covered.

## Status

landed 20261020T221229-L-4161399 2026-10-20 (merge of deliver/J9/Sheaf.RingTheory.KoszulRoofComparisonIndependence)
