/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData
import WeilConjectures.SixFunctors.CoefPairingNativeFrameComparison

/-! # Compactification realization of the finite tower pairing

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2,
compact-support and finite projection word
(blueprint: lem-coef-pairing-compactification-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d v w v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CoefPairingFrame
variable {V : Type a} {W : Type b} [Category.{v} V] [Category.{w} W]
  (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
  (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW)
@[reassoc] private theorem compactification_leftMate_first (H H' : V) (M : W) (f : H ⟶ H') :
    TV.map (Prod.mkHom f (𝟙 _)) ≫ leftMate TV TW L G adj mu H' M =
      leftMate TV TW L G adj mu H M ≫
        G.map (TW.map (Prod.mkHom (L.map f) (𝟙 _))) := by
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  let t := adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)
  exact NatTrans.naturality (t.app M) f
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame TA TB TC TD J P R RX)

private theorem compactification_openTensor_naturality (L L' : B) (M M' : A)
    (f : L ⟶ L') (g : M ⟶ M') :
    J.map (TA.map (Prod.mkHom (F.jstar.map f) g)) ≫ (F.openTensor L' M').hom =
      (F.openTensor L M).hom ≫ TB.map (Prod.mkHom f (J.map g)) := by
  apply (F.openAdjunction.homEquiv _ _).injective
  rw [F.openAdjunction.homEquiv_naturality_left,
    F.openAdjunction.homEquiv_naturality_right,
    F.openTensor_adjunct, F.openTensor_adjunct]
  have hn := F.restrictionTensor.inv.naturality (Prod.mkHom f (J.map g))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [Category.assoc, ← hn]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2
  ext <;> simp


@[reassoc] private theorem compactification_openTensor_inv_naturality (L L' : B) (M M' : A)
    (f : L ⟶ L') (g : M ⟶ M') :
    TB.map (Prod.mkHom f (J.map g)) ≫ (F.openTensor L' M').inv =
      (F.openTensor L M).inv ≫ J.map (TA.map (Prod.mkHom (F.jstar.map f) g)) := by
  apply (cancel_epi (F.openTensor L M).hom).mp
  rw [← Category.assoc, ← compactification_openTensor_naturality F L L' M M' f g]
  simp

@[reassoc] private theorem compactification_projection_first (H H' : D) (M : A) (h : H ⟶ H') :
    TD.map (Prod.mkHom h (𝟙 _)) ≫ F.projection H' M =
      F.projection H M ≫ R.map (P.map (J.map
        (TA.map (Prod.mkHom (F.jstar.map (F.pstar.map (F.sstar.map h))) (𝟙 M))))) := by
  dsimp only [projection]
  simp only [Category.assoc]
  rw [compactification_leftMate_first_assoc]
  simp only [← R.map_comp]
  apply congrArg (fun t ↦ _ ≫ R.map t)
  rw [← Category.assoc, compactification_leftMate_first, Category.assoc, ← P.map_comp]
  have hn := compactification_openTensor_inv_naturality F _ _ M M
    (F.pstar.map (F.sstar.map h)) (𝟙 M)
  simp only [Functor.map_id] at hn
  rw [hn]
  simp only [Functor.map_comp]


private theorem compactification_pairing_target
    {HA : Aᵒᵖ × A ⥤ A} (S : WeilConjectures.CoefficientClosedStructure HA)
    (F : CoefPairingFrame S.tensor TB TC TD J P R RX)
    (M Q Q' : A) (g : Q ⟶ Q') :
    TD.map (Prod.mkHom (RX.map (HA.map (Prod.mkHom (𝟙 (op M)) g))) (𝟙 _)) ≫
        F.pairing S rfl M Q' =
      F.pairing S rfl M Q ≫ R.map (P.map (J.map g)) := by
  let h := HA.map (Prod.mkHom (𝟙 (op M)) g)
  have hc := F.sourceAdjunction.counit.naturality h
  have he : S.tensor.map (Prod.mkHom h (𝟙 M)) ≫ S.evaluation M Q' =
      S.evaluation M Q ≫ g := by
    let := S.monoidal
    have hn := (S.adjunction M).counit.naturality g
    change (h ▷ M) ≫ S.evaluation M Q' = S.evaluation M Q ≫ g at hn
    have ht : S.tensor.map (Prod.mkHom h (𝟙 M)) = h ⊗ₘ 𝟙 M := rfl
    rw [ht, MonoidalCategory.tensorHom_id]
    exact hn
  dsimp only [pairing]
  simp only [eqToHom_refl, Category.id_comp]
  rw [compactification_projection_first_assoc]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  congr 3
  dsimp only [Functor.comp_map] at hc
  rw [← Category.assoc, ← Functor.map_comp]
  have ht :
      Prod.mkHom (F.jstar.map (F.pstar.map (F.sstar.map (RX.map h)))) (𝟙 M) ≫
        Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q'))) (𝟙 M) =
      Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M) ≫
        Prod.mkHom h (𝟙 M) := by
    apply Prod.ext
    · exact hc
    · simp
  rw [ht, Functor.map_comp, Category.assoc, he]

end CategoryTheory.CoefPairingFrame

attribute [local instance 1] WeilConjectures.coefHomFinitePointHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (D : FiniteFieldDatum.{u}) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private def compactificationHomTargetIso (n : ℕ)
    {N N' : normalizedDVRDerived.{u, u} l E X n} (e : N ≅ N') :
    coefPairingFiniteHom l E X n N ≅ coefPairingFiniteHom l E X n N' :=
  NatIso.ofComponents (fun K ↦
    (coefPairingFiniteSections l E X n).mapIso
      ((coefficientFiniteInternalHom l E X n).mapIso
        (Iso.prod (Iso.refl ((scalarReductionDerivedExtension l E X n).op.obj K)) e)))
    (by
      intro K L f
      dsimp only [coefPairingFiniteHom, Functor.comp_map, Functor.comp_obj,
        Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Prod.sectL_map]
      simp only [← Functor.map_comp]
      congr 2
      ext <;> simp)

/-- Realize the native quotient-site projection word in the fixed compactification
frame, including its finite comparisons. This concerns compact-support realization
and finite normalization, independently of the Hom representative calculation and
of dinaturality of the resulting morphism.

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, extracted
steps 4--9; Stacks 07A6, 0B56 and 0941
(blueprint: lem-coef-pairing-compactification-models).

Proof: apply projectionEvaluation over D.k, whose characteristic is different
from l, to obtain the native system model and its scalar specialization. Apply
pairingFiniteNormalization to obtain finite evaluation data and the native
finite-normalization equation. The separate native/frame comparison theorem
supplies the coherent calculus, system and finite frames, their Hom/support
comparisons, and the two word comparisons. Map the native finite-normalization
equation through the equivalence of point localization models, and conjugate by
the source and target comparison isomorphisms. The two word comparisons then give
the required pairing equality with the actual finite evaluation of Q as target.
Finally compose the finite Hom comparison with the natural Hom isomorphism induced
by eQ, and compose compact-support comparison with finite support applied to eQ.
Covariance of the general frame pairing in its second input, proved from the
projection mates and closed evaluation counit naturality, transports the equality
to the prescribed finite dualizing terms. The support-transition equation is
unchanged. No trace or faithfulness of finite derived evaluation is used. -/
theorem coefPairingCompactificationModels (hl : l ≠ D.p)
    (Q : CochainComplex (coefficientSequenceModules.{u, u} l E X) ℤ)
    (eQ : ∀ n : ℕ,
      (coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q) ≅
        integralDualizingFiniteTerm l E D X n) :
    ∃ (S : CoefficientDerivedSystemCalculus l E X)
      (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
      (F : ∀ n : ℕ,
        CoefPairingFiniteFrame l E (finiteDualizingCompactification D X) S G n)
      (evaluationTensor : ∀ n : ℕ,
        coefPairingTensor l E ⋙ coefTraceEvaluation l E n ≅
          (coefTraceEvaluation l E n).prod (coefTraceEvaluation l E n) ⋙
            MonoidalCategory.tensor
              (DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))))
      (eH : ∀ n : ℕ,
        coefPairingHom l E X S Q ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteHom l E X n (integralDualizingFiniteTerm l E D X n))
      (eB : ∀ n : ℕ,
        coefPairingSupport l E D X S ⋙ coefTraceEvaluation l E n ≅
          coefPairingFiniteC l E D X n)
      (eQcompact : ∀ n : ℕ,
        (coefTraceEvaluation l E n).obj (coefTraceDualizingTower l E D X Q) ≅
          (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).obj
            (integralDualizingFiniteTerm l E D X n)),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        {m n : ℕ} (h : n ≤ m),
        (coefTraceTransition l E h).app ((coefPairingSupport l E D X S).obj K) ≫
          (eB n).hom.app K =
        (eB m).hom.app K ≫
          (coefPairingIntegralSections l E (Spec (.of D.k))).map
            (compactSupportRestrictedTransition l E (finiteDualizingCompactification D X)
              m n h K)) ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X)),
        finiteTorConstructibleIntegral l E X K → ∀ n : ℕ,
        (coefTraceEvaluation l E n).map
            (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫
          (eQcompact n).hom =
        (evaluationTensor n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              (integralDualizingFiniteTerm l E D X n)) := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hcard : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hcard
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hunit : IsUnit (l : D.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out) hl.symm)
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : (X ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  obtain ⟨m, ⟨s⟩⟩ := CoefProjectionEvaluation.projectionEvaluation l E D.k X
    (Spec (.of D.k)) (X ↘ Spec (.of D.k)) hunit (finiteDualizingCompactification D X)
  have he := CoefProjectionEvaluation.pairingFiniteNormalization l E D.k X
    (Spec (.of D.k)) (X ↘ Spec (.of D.k)) hunit (finiteDualizingCompactification D X) m s
  choose e he using he
  obtain ⟨V, S, G, F, t, eH, eB, eC, a, c, hB, hsystem, hfinite⟩ :=
    coefPairingNativeFrameComparison l E D X m s e Q
  have hraw (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) (n : ℕ) :
      (coefTraceEvaluation l E n).map
          (G.beta l E (S.reduction.obj K) (coefTraceInput l E X Q)) ≫ (eC n).hom =
        (t n).hom.app
            ((coefPairingHom l E X S Q).obj (op K), (coefPairingSupport l E D X S).obj K) ≫
          ((eH n).hom.app (op K) ⊗ₘ (eB n).hom.app K) ≫
            coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
              ((scalarReductionDerivedExtension l E X n).obj K)
              ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
                (coefTraceInput l E X Q)) := by
    rw [hsystem, hfinite]
    simpa only [Category.assoc] using
      congrArg (fun z ↦ (a K n).hom ≫ V.functor.map z ≫ (c n).hom)
        (he n K (coefTraceInput l E X Q))
  let eH' (n : ℕ) := eH n ≪≫ compactificationHomTargetIso l E X n (eQ n)
  let eC' (n : ℕ) := eC n ≪≫
    (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).mapIso (eQ n)
  refine ⟨S, G, F, t, eH', eB, eC', hB, ?_⟩
  intro K _hK n
  have hn := CategoryTheory.CoefPairingFrame.compactification_pairing_target
    (S.finiteClosed n) (F n)
    ((scalarReductionDerivedExtension l E X n).obj K)
    ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj (coefTraceInput l E X Q))
    (integralDualizingFiniteTerm l E D X n) (eQ n).hom
  dsimp only [eC', Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, hraw]
  dsimp only [eH', Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  have hn' :
      (((compactificationHomTargetIso l E X n (eQ n)).hom.app (op K)) ⊗ₘ
          𝟙 ((coefPairingFiniteC l E D X n).obj K)) ≫
        coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
          ((scalarReductionDerivedExtension l E X n).obj K)
          (integralDualizingFiniteTerm l E D X n) =
      coefPairingFiniteBeta l E (finiteDualizingCompactification D X) S G n (F n)
          ((scalarReductionDerivedExtension l E X n).obj K)
          ((coefficientSequenceDerivedEvaluation.{u, u} l E X n).obj
            (coefTraceInput l E X Q)) ≫
        (coefPairingFiniteSupport l E (finiteDualizingCompactification D X) n).map
          (eQ n).hom := by
    exact hn
  rw [← hn']
  simp only [← Category.assoc]
  congr 1
  rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

end WeilConjectures
