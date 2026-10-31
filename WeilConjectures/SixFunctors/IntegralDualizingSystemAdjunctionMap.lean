/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSupportSystemHom

/-! # The exceptional mapping comparison defined by a system trace

Source: prop-coef-integral-dualizing, second paragraph, the projection/evaluation
and exceptional-counit transpose (blueprint: def-coef-system-exceptional-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CoefPairingFrame

variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {HA : Aᵒᵖ × A ⥤ A} {HC : Cᵒᵖ × C ⥤ C}
  (SA : WeilConjectures.CoefficientClosedStructure HA)
  (SC : WeilConjectures.CoefficientClosedStructure HC)
  {TB : B × B ⥤ B} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame SA.tensor TB SC.tensor TD J P R RX)

/-- Projection and evaluation before applying base sections. This retains the base
quotient scalars, so a trace into the base unit can be transposed there.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-exceptional-transpose). -/
def basePairing (M Q : A) :
    SC.tensor.obj (F.sstar.obj (RX.obj (HA.obj (op M, Q))), P.obj (J.obj M)) ⟶
      P.obj (J.obj Q) :=
  leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj (RX.obj (HA.obj (op M, Q)))) (J.obj M) ≫
    P.map (F.openTensor (F.pstar.obj (F.sstar.obj (RX.obj (HA.obj (op M, Q))))) M).inv ≫
    P.map (J.map
      (SA.tensor.map
          (Prod.mkHom (F.sourceAdjunction.counit.app (HA.obj (op M, Q))) (𝟙 M)) ≫
        SA.evaluation M Q))

/-- The actual exceptional comparison, transposed first over the base quotient ring
and then under base sections. No family of evaluated arrows is lifted.
Source: prop-coef-integral-dualizing, paragraph 2
(blueprint: def-coef-system-exceptional-transpose). -/
def exceptionalMap (Q : A) (U : C) (t : P.obj (J.obj Q) ⟶ U) (M : A) :
    RX.obj (HA.obj (op M, Q)) ⟶ R.obj (HC.obj (op (P.obj (J.obj M)), U)) :=
  F.sectionsAdjunction.homEquiv _ _
    (SC.transpose _ _ _ (basePairing SA SC F M Q ≫ t))

@[reassoc] private theorem mate_first
    (H H' : C) (M : B) (f : H ⟶ H') :
    SC.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor H' M =
      leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor H M ≫
        P.map (TB.map (Prod.mkHom (F.pstar.map f) (𝟙 _))) := by
  let flip := (Functor.flipping (C := C) (D := C) (E := B)).functor
  let w := F.properAdjunction.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj SC.tensor).flip)
    (flip.map (Functor.curry.map F.properTensor.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp F.pstar F.pstar TB)).hom)
  exact NatTrans.naturality (w.app M) f

@[reassoc] private theorem mate_second
    (H : C) (M M' : B) (g : M ⟶ M') :
    SC.tensor.map (Prod.mkHom (𝟙 H) (P.map g)) ≫
        leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor H M' =
      leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor H M ≫
        P.map (TB.map (Prod.mkHom (𝟙 _) g)) := by
  let flip := (Functor.flipping (C := C) (D := C) (E := B)).functor
  let w := F.properAdjunction.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj SC.tensor).flip)
    (flip.map (Functor.curry.map F.properTensor.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp F.pstar F.pstar TB)).hom)
  exact NatTrans.naturality_app w H g

private theorem open_naturality (L L' : B) (M M' : A)
    (f : L ⟶ L') (g : M ⟶ M') :
    J.map (SA.tensor.map (Prod.mkHom (F.jstar.map f) g)) ≫
        (F.openTensor L' M').hom =
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

@[reassoc] private theorem open_inv_naturality (L L' : B) (M M' : A)
    (f : L ⟶ L') (g : M ⟶ M') :
    TB.map (Prod.mkHom f (J.map g)) ≫ (F.openTensor L' M').inv =
      (F.openTensor L M).inv ≫ J.map (SA.tensor.map (Prod.mkHom (F.jstar.map f) g)) := by
  apply (cancel_epi (F.openTensor L M).hom).mp
  rw [← Category.assoc, ← open_naturality SA SC F L L' M M' f g]
  simp

/-- The base pairing is dinatural in its compact-support argument. In particular
this is an equality of whole-system maps, before evaluating any finite level.
Source: naturality of projection mates and closed evaluation, Stacks 08J9
(blueprint: def-coef-system-exceptional-transpose).
Proof: move the first input through the proper mate and inverse open comparison.
The source counit is natural, and evaluation is dinatural in M. Move the resulting
map on M back through the inverse open comparison and the proper mate. -/
theorem basePairing_dinaturality (M M' Q : A) (f : M ⟶ M') :
    SC.tensor.map
        (Prod.mkHom (F.sstar.map (RX.map (HA.map (Prod.mkHom f.op (𝟙 Q))))) (𝟙 _)) ≫
      basePairing SA SC F M Q =
    SC.tensor.map (Prod.mkHom (𝟙 _) (P.map (J.map f))) ≫
      basePairing SA SC F M' Q := by
  let h := HA.map (Prod.mkHom f.op (𝟙 Q))
  have hc := F.sourceAdjunction.counit.naturality h
  have he : SA.tensor.map (Prod.mkHom h (𝟙 M)) ≫ SA.evaluation M Q =
      SA.tensor.map (Prod.mkHom (𝟙 _) f) ≫ SA.evaluation M' Q := by
    let := SA.monoidal
    have hh := SA.evaluation_naturality M' M Q f
    change (h ▷ M) ≫ SA.evaluation M Q = (_ ◁ f) ≫ SA.evaluation M' Q at hh
    simpa only [WeilConjectures.CoefficientClosedStructure.tensor,
      MonoidalCategory.tensor, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom] using hh
  dsimp only [basePairing]
  rw [mate_first_assoc SA SC F, mate_second_assoc SA SC F]
  simp only [← P.map_comp]
  congr 1
  have hn := open_inv_naturality SA SC F _ _ M M
    (F.pstar.map (F.sstar.map (RX.map h))) (𝟙 M)
  have hn' := open_inv_naturality SA SC F _ _ M M'
    (𝟙 (F.pstar.obj (F.sstar.obj (RX.obj (HA.obj (op M', Q)))))) f
  simp only [Functor.map_id] at hn hn'
  simp only [← Category.assoc]
  rw [hn, hn']
  simp only [Category.assoc, ← J.map_comp]
  congr 3
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

private theorem transpose_source (T V V' U : C) (f : V ⟶ V')
    (g : SC.tensor.obj (T, V') ⟶ U) :
    SC.transpose T V U (SC.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      SC.transpose T V' U g ≫ HC.map (Prod.mkHom f.op (𝟙 U)) := by
  let := SC.monoidal
  have he : (SC.transpose T V' U g ▷ V') ≫ SC.evaluation V' U = g := by
    have hh := ((SC.adjunction V').homEquiv T U).symm_apply_apply g
    rw [Adjunction.homEquiv_counit] at hh
    exact hh
  have hn := SC.evaluation_naturality V' V U f
  change (_ ▷ V) ≫ SC.evaluation V U = (_ ◁ f) ≫ SC.evaluation V' U at hn
  apply (SC.transpose T V U).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = ((SC.adjunction V).homEquiv T U).symm _
  rw [Adjunction.homEquiv_counit, Functor.map_comp]
  change SC.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g =
    ((SC.transpose T V' U g ▷ V) ≫ (HC.map (Prod.mkHom f.op (𝟙 U)) ▷ V)) ≫
      SC.evaluation V U
  rw [Category.assoc, hn, ← Category.assoc]
  have hx : (SC.transpose T V' U g ▷ V) ≫ (_ ◁ f) =
      (T ◁ f) ≫ (SC.transpose T V' U g ▷ V') := by
    exact (whisker_exchange _ _).symm
  rw [hx, Category.assoc, he]
  simp only [WeilConjectures.CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor, MonoidalCategory.id_tensorHom]

/-- Transposing the base pairing gives a contravariantly natural comparison.
Source: Stacks 08J9 and 07A6 (blueprint: def-coef-system-exceptional-transpose).
Proof: apply the two adjunction bijections backwards. Their naturality converts
the desired square into the dinaturality square of basePairing, followed by t. -/
theorem exceptionalMap_naturality (Q : A) (U : C) (t : P.obj (J.obj Q) ⟶ U)
    (M M' : A) (f : M ⟶ M') :
    RX.map (HA.map (Prod.mkHom f.op (𝟙 Q))) ≫ exceptionalMap SA SC F Q U t M =
      exceptionalMap SA SC F Q U t M' ≫
        R.map (HC.map (Prod.mkHom (P.map (J.map f)).op (𝟙 U))) := by
  unfold exceptionalMap
  rw [← F.sectionsAdjunction.homEquiv_naturality_left,
    ← F.sectionsAdjunction.homEquiv_naturality_right]
  congr 1
  let := SC.monoidal
  let h := RX.map (HA.map (Prod.mkHom f.op (𝟙 Q)))
  have hc := (SC.adjunction (P.obj (J.obj M))).homEquiv_naturality_left
    (F.sstar.map h) (basePairing SA SC F M Q ≫ t)
  change (SC.adjunction (P.obj (J.obj M))).homEquiv _ _
      ((F.sstar.map h ▷ _) ≫ (basePairing SA SC F M Q ≫ t)) = _ at hc
  have hc' : SC.transpose _ _ _
      (SC.tensor.map (Prod.mkHom (F.sstar.map h) (𝟙 _)) ≫
        (basePairing SA SC F M Q ≫ t)) =
      F.sstar.map h ≫ SC.transpose _ _ _ (basePairing SA SC F M Q ≫ t) := by
    simp only [WeilConjectures.CoefficientClosedStructure.transpose,
      WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor,
      MonoidalCategory.tensorHom_id]
    convert hc using 1 <;> rfl
  rw [← hc', ← Category.assoc, basePairing_dinaturality SA SC F M M' Q f,
    Category.assoc]
  exact transpose_source SC _ _ _ _ (P.map (J.map f)) (basePairing SA SC F M' Q ≫ t)

end CategoryTheory.CoefPairingFrame

namespace WeilConjectures
universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Exact finite evaluation of the underlying strict scalar-module tower.
Source: Stacks 05RU (blueprint: def-coef-system-exceptional-transpose). -/
abbrev coefPairingDerivedEvaluation (n : ℕ) : coefPairingDerived l E ⥤
    DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) :=
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj (op n)).mapDerivedCategory

/-- Exact evaluation detects invertibility of an already constructed tower map.
Source: Stacks 015F, 05RU (blueprint: def-coef-system-exceptional-transpose).
Proof: commute evaluation with cohomology. An arrow of strict towers is invertible
if every component is, and the cohomology functors jointly detect derived isomorphisms. -/
theorem coefPairingDerived_isIso_of_evaluations {M N : coefPairingDerived l E}
    (f : M ⟶ N) (hf : ∀ n : ℕ, IsIso ((coefPairingDerivedEvaluation l E n).map f)) :
    IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro i
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro n
  let ev := (evaluation ℕᵒᵖ (ModuleCat.{u + 1} (coefTraceRing l E))).obj n
  have := hf n.unop
  have hi : IsIso ((DerivedCategory.homologyFunctor _ i).map
      ((coefPairingDerivedEvaluation l E n.unop).map f)) := inferInstance
  exact (NatIso.isIso_map_iff (ev.mapDerivedCategoryHomologyFunctorIso i) f).2 hi
end WeilConjectures
