/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefTowerEvaluationPairingData

/-! # Dinaturality of compact-support evaluation frames

Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, step 10
(blueprint: lem-coef-pairing-frame-dinaturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b c d v w v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CoefPairingFrame
variable {V : Type a} {W : Type b} [Category.{v} V] [Category.{w} W]
  (TV : V × V ⥤ V) (TW : W × W ⥤ W) (L : V ⥤ W) (G : W ⥤ V)
  (adj : L ⊣ G) (mu : TV ⋙ L ≅ L.prod L ⋙ TW)
@[reassoc] private theorem leftMate_first (H H' : V) (M : W) (f : H ⟶ H') :
    TV.map (Prod.mkHom f (𝟙 _)) ≫ leftMate TV TW L G adj mu H' M =
      leftMate TV TW L G adj mu H M ≫
        G.map (TW.map (Prod.mkHom (L.map f) (𝟙 _))) := by
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  let t := adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)
  exact NatTrans.naturality (t.app M) f
@[reassoc] private theorem leftMate_second (H : V) (M M' : W) (g : M ⟶ M') :
    TV.map (Prod.mkHom (𝟙 _) (G.map g)) ≫ leftMate TV TW L G adj mu H M' =
      leftMate TV TW L G adj mu H M ≫ G.map (TW.map (Prod.mkHom (𝟙 _) g)) := by
  let flip := (Functor.flipping (C := V) (D := V) (E := W)).functor
  let t := adj.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TW).flip) (T_D := (Functor.curryObj TV).flip)
    (flip.map (Functor.curry.map mu.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp L L TW)).hom)
  exact NatTrans.naturality_app t H g

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame TA TB TC TD J P R RX)

private theorem openTensor_naturality (L L' : B) (M M' : A)
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


@[reassoc] private theorem openTensor_inv_naturality (L L' : B) (M M' : A)
    (f : L ⟶ L') (g : M ⟶ M') :
    TB.map (Prod.mkHom f (J.map g)) ≫ (F.openTensor L' M').inv =
      (F.openTensor L M).inv ≫ J.map (TA.map (Prod.mkHom (F.jstar.map f) g)) := by
  apply (cancel_epi (F.openTensor L M).hom).mp
  rw [← Category.assoc, ← openTensor_naturality F L L' M M' f g]
  simp

@[reassoc] private theorem projection_first (H H' : D) (M : A) (h : H ⟶ H') :
    TD.map (Prod.mkHom h (𝟙 _)) ≫ F.projection H' M =
      F.projection H M ≫ R.map (P.map (J.map
        (TA.map (Prod.mkHom (F.jstar.map (F.pstar.map (F.sstar.map h))) (𝟙 M))))) := by
  dsimp only [projection]
  simp only [Category.assoc]
  rw [leftMate_first_assoc]
  simp only [← R.map_comp]
  apply congrArg (fun t ↦ _ ≫ R.map t)
  rw [← Category.assoc, leftMate_first, Category.assoc, ← P.map_comp]
  have hn := openTensor_inv_naturality F _ _ M M
    (F.pstar.map (F.sstar.map h)) (𝟙 M)
  simp only [Functor.map_id] at hn
  rw [hn]
  simp only [Functor.map_comp]

@[reassoc] private theorem projection_second (H : D) (M M' : A) (g : M ⟶ M') :
    TD.map (Prod.mkHom (𝟙 H) (R.map (P.map (J.map g)))) ≫ F.projection H M' =
      F.projection H M ≫ R.map (P.map (J.map
        (TA.map (Prod.mkHom (𝟙 _) g)))) := by
  dsimp only [projection]
  simp only [Category.assoc]
  rw [leftMate_second_assoc]
  simp only [← R.map_comp]
  apply congrArg (fun t ↦ _ ≫ R.map t)
  rw [← Category.assoc, leftMate_second, Category.assoc, ← P.map_comp]
  rw [openTensor_inv_naturality]
  simp only [Functor.map_id, Functor.map_comp]

@[reassoc] private theorem pairing_dinaturality {HA : Aᵒᵖ × A ⥤ A}
    (S : WeilConjectures.CoefficientClosedStructure HA)
    (F : CoefPairingFrame S.tensor TB TC TD J P R RX)
    (M M' Q : A) (f : M ⟶ M') :
    TD.map (Prod.mkHom (RX.map (HA.map (Prod.mkHom f.op (𝟙 Q)))) (𝟙 _)) ≫
        F.pairing S rfl M Q =
      TD.map (Prod.mkHom (𝟙 _) (R.map (P.map (J.map f)))) ≫
        F.pairing S rfl M' Q := by
  let h := HA.map (Prod.mkHom f.op (𝟙 Q))
  have hc := F.sourceAdjunction.counit.naturality h
  have he : S.tensor.map (Prod.mkHom h (𝟙 M)) ≫ S.evaluation M Q =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation M' Q :=
    by
      let := S.monoidal
      have he := S.evaluation_naturality M' M Q f
      change (h ▷ M) ≫ S.evaluation M Q =
        (_ ◁ f) ≫ S.evaluation M' Q at he
      simpa only [WeilConjectures.CoefficientClosedStructure.tensor,
        MonoidalCategory.tensor, MonoidalCategory.tensorHom_id,
        MonoidalCategory.id_tensorHom] using he
  dsimp only [pairing]
  simp only [eqToHom_refl, Category.id_comp]
  rw [projection_first_assoc, projection_second_assoc]
  congr 1
  simp only [← Functor.map_comp]
  congr 3
  dsimp only [Functor.comp_map] at hc
  rw [← Category.assoc, ← Functor.map_comp]
  have ht :
      Prod.mkHom (F.jstar.map (F.pstar.map (F.sstar.map (RX.map h)))) (𝟙 M) ≫
        Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M) =
      Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M', Q))) (𝟙 M) ≫
        Prod.mkHom h (𝟙 M) := by
    apply Prod.ext
    · exact hc
    · simp
  rw [ht, Functor.map_comp, Category.assoc, he]
  simp only [← Category.assoc, ← Functor.map_comp]
  congr 2
  ext <;> simp

end CategoryTheory.CoefPairingFrame

namespace WeilConjectures
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Dinaturality of the actual compact-support frame pairing on whole systems.
Source: blueprint prop-coef-integral-dualizing, proof paragraph 2, step 10
(blueprint: lem-coef-pairing-frame-dinaturality).

Proof: the projection mates are natural in each tensor argument. The open tensor
comparison is natural because its prescribed adjunct is tensor of the open unit
followed by the natural inverse restriction comparison. Move the Hom source map
through these three projection factors, use source-counit naturality, then closed
evaluation dinaturality. Finally move the compact-support input map back through
the factors and use naturality of compactSections. This is equality in the whole
derived tower category before finite evaluation, trace or inverse limit. -/
theorem coefPairingSystem_dinaturality {X Y : Scheme.{u}} {a : X ⟶ Y}
    {c : Compactification a} {S : CoefficientDerivedSystemCalculus l E X}
    (G : CoefPairingSystem l E c S)
    (M M' Q : coefficientSequenceDerived.{u, u} l E X) (f : M ⟶ M') :
    (coefPairingTensor l E).map
        (Prod.mkHom ((coefPairingSections l E X).map
          ((coefficientSequenceInternalHom l E X).map (Prod.mkHom f.op (𝟙 Q)))) (𝟙 _)) ≫
        G.beta l E M Q =
      (coefPairingTensor l E).map
        (Prod.mkHom (𝟙 _) ((coefTraceCompactSections l E c).map f)) ≫
        G.beta l E M' Q := by
  dsimp only [CoefPairingSystem.beta]
  simp only [← Category.assoc, ← Functor.map_comp]
  have ht :
      Prod.mkHom ((coefPairingSections l E X).map
          ((coefficientSequenceInternalHom l E X).map (Prod.mkHom f.op (𝟙 Q)))) (𝟙 _) ≫
        Prod.mkHom (𝟙 _) (G.compactSections.inv.app M) =
      Prod.mkHom (𝟙 _) (G.compactSections.inv.app M) ≫
        Prod.mkHom ((coefPairingSections l E X).map
          ((coefficientSequenceInternalHom l E X).map (Prod.mkHom f.op (𝟙 Q)))) (𝟙 _) := by
    ext <;> simp
  rw [ht, Functor.map_comp]
  simp only [Category.assoc]
  have hd := CategoryTheory.CoefPairingFrame.pairing_dinaturality
    S.systemClosed G.frame M M' Q f
  have hd' := congrArg (fun t ↦ t ≫ G.compactSections.hom.app Q) hd
  simp only [Category.assoc] at hd'
  dsimp only [Functor.comp_obj] at *
  erw [hd']
  have hn := G.compactSections.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← Functor.map_comp]
  congr 1
  congr 1
  ext <;> simp [hn]

end WeilConjectures
