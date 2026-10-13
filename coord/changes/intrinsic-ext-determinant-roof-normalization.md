# ExteriorAlgebra.intrinsic_ext_determinant_roof

## Reason

Quotient linearity does not determine normalization. For A = Q, r = 0, I = 0, the empty sequence is Koszul-regular. Negating the canonical Ext^0 equivalence preserves quotient linearity, but sends the identity roof to -1, while the formula requires +1. The existing STATEMENT-DISPUTED comment already records this fault. Following Stacks Tag 0BQZ, assert existence of a normalized equivalence instead.

## Old

```lean
theorem intrinsic_ext_determinant_roof
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I)
    (e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
      koszulNormalDeterminant A I r)
    (hmul : ∀ (b : A ⧸ I)
      (x : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r),
      e ((Abelian.Ext.mk₀ (ModuleCat.ofHom
        (b • (LinearMap.id : (A ⧸ I) →ₗ[A] (A ⧸ I))))).comp x (zero_add r)) =
        @SMul.smul (A ⧸ I) (⋀[A ⧸ I]^r (Module.Dual (A ⧸ I) I.Cotangent))
          inferInstance b (e x)) :
    ∀ (f : Fin r → A) (_hreg : RingTheory.Sequence.IsKoszulRegular f)
        (hf : Ideal.span (Set.range f) = I)
        (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
            (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
          (v : Fin r → (Fin r →₀ A)),
          exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
            (e ((Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A))))
            (exteriorPower.ιMulti (A ⧸ I) r
              (fun i ↦ koszulConormalVector A I r f hf (v i))) =
            (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
            Ideal.Quotient.mk I
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                (ModuleCat.of A A)).hom
                (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
                  ComplexShape.embeddingDownNat (i := r) rfl).inv
                (exteriorPower.ιMulti A r v))))
```

## New

```lean
theorem intrinsic_ext_determinant_roof
    (A : Type uT) [CommRing A] [HasDerivedCategory.{uT + 1} (ModuleCat.{uT} A)]
    (I : Ideal A) (r : ℕ)
    (hex : ∃ f : Fin r → A,
      RingTheory.Sequence.IsKoszulRegular f ∧ Ideal.span (Set.range f) = I) :
    ∃ e : Abelian.Ext (ModuleCat.of A (A ⧸ I)) (ModuleCat.of A A) r ≃ₗ[A]
      koszulNormalDeterminant A I r,
    ∀ (f : Fin r → A) (_hreg : RingTheory.Sequence.IsKoszulRegular f)
        (hf : Ideal.span (Set.range f) = I)
        (ε : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
          (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I)))
        [QuasiIso ε],
        (∀ x : ⋀[A]^0 (Fin r →₀ A),
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (ModuleCat.of A (A ⧸ I))).hom
            (ε.f 0 (((koszulComplex A r f).extendXIso
              ComplexShape.embeddingDownNat (i := 0) rfl).inv x)) =
          Ideal.Quotient.mk I (exteriorPower.zeroEquiv A (Fin r →₀ A) x)) →
        ∀ (z : (koszulComplex A r f).extend ComplexShape.embeddingDownNat ⟶
            (CochainComplex.singleFunctor (ModuleCat A) (-(r : ℤ))).obj (ModuleCat.of A A))
          (v : Fin r → (Fin r →₀ A)),
          exteriorPower.pairingDual (A ⧸ I) I.Cotangent r
            (e ((Abelian.Ext.homLinearEquiv (R := A)).symm
              (inv (DerivedCategory.Q.map ε) ≫ DerivedCategory.Q.map z ≫
                ((DerivedCategory.singleFunctors (ModuleCat A)).shiftIso
                  (r : ℤ) (-(r : ℤ)) 0 (add_neg_cancel (r : ℤ))).inv.app
                    (ModuleCat.of A A))))
            (exteriorPower.ιMulti (A ⧸ I) r
              (fun i ↦ koszulConormalVector A I r f hf (v i))) =
            (-1 : A ⧸ I) ^ (r * (r - 1) / 2) *
            Ideal.Quotient.mk I
              ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-(r : ℤ))
                (ModuleCat.of A A)).hom
                (z.f (-(r : ℤ)) (((koszulComplex A r f).extendXIso
                  ComplexShape.embeddingDownNat (i := r) rfl).inv
                (exteriorPower.ιMulti A r v))))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulRegularSequenceDualComplex | A4 | The intrinsic theorem obtains the normalized e from the corrected existential theorem and proves quotient linearity of that same e directly. All other signatures and visibility are identical. |

tools/downstream.py reports 299 transitive importers, and --uses reports only this module as a textual user. None of the 299 importers uses the changed declaration or needs adaptation. No target statement or public definition changes; the statements and definitions used by the targets retain their meanings. No separately held module is adapted.

## Status

landed 20261013T045510-L-124009 2026-10-13 (merge of deliver/A4/Sheaf.RingTheory.KoszulRegularSequenceDualComplex)
