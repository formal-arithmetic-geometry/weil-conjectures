/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluation
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible

import WeilConjectures.SixFunctors.Completed.CompletedTensorScalarLinearity
import WeilConjectures.SixFunctors.Normalized.NormalizedRationalEvaluationNaturality
import WeilConjectures.SixFunctors.Supporting.Tensor.LocalizedTensorBraidingNaturality

/-! # Completed and rational tensor-Hom transposition

Source: Weil blueprint main-20261015, sec-six-functors/sk-thm-sf-package,
cor-coef-verdier-weil-equivariance, proof paragraph 2; Stacks 08J9, 08JA, 099B, 099M
(blueprint: lem-coef-completed-tensor-hom-transpose).

The completed evaluation is the normalized Hom-first counit preceded by the
canonical signed braiding. Rational scalar multiplication is written through
sfRationalCoefficientEquiv, the canonical identification of the localized ring with E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u a b
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem ambientEvaluation_naturality
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q P' Q' : D)
    (f : P' ⟶ P) (g : Q ⟶ Q') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 P')) ≫
        S.evaluation P' Q' =
      S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q ≫ g := by
  let := S.monoidal
  have he : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P')) ≫
      S.evaluation P' Q = S.tensor.map (Prod.mkHom (𝟙 _) f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      S.evaluation_naturality P P' Q f
  have hg : S.tensor.map (Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P')) ≫
      S.evaluation P' Q' = S.evaluation P' Q ≫ g := by
    simpa [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation] using
      (S.adjunction P').counit.naturality g
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh]
  have ht : Prod.mkHom
      (H.map (Prod.mkHom f.op (𝟙 Q)) ≫ H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') =
      Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 Q))) (𝟙 P') ≫
        Prod.mkHom (H.map (Prod.mkHom (𝟙 (op P')) g)) (𝟙 P') := by
    ext <;> simp
  rw [ht, S.tensor.map_comp, Category.assoc, hg, ← Category.assoc, he]
  exact Category.assoc _ _ _

private theorem ambientInverseTranspose_naturality
    {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (L L' P Q P' Q' : D)
    (f : L' ⟶ L) (g : P' ⟶ P) (h : Q ⟶ Q') (phi : L ⟶ H.obj (op P, Q)) :
    (S.transpose L' P' Q').symm (f ≫ phi ≫ H.map (Prod.mkHom g.op h)) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose L P Q).symm phi ≫ h := by
  let := S.monoidal
  have he (T P Q : D) (psi : T ⟶ H.obj (op P, Q)) :
      (S.transpose T P Q).symm psi =
        S.tensor.map (Prod.mkHom psi (𝟙 P)) ≫ S.evaluation P Q :=
    by
      have ht : S.tensor.map (Prod.mkHom psi (𝟙 P)) =
          (@MonoidalCategory.tensorRight D _ S.monoidal P).map psi :=
        @MonoidalCategory.tensorHom_id D _ S.monoidal T _ psi P
      rw [ht]
      exact (S.adjunction P).homEquiv_counit (g := psi)
  rw [he, he, Category.assoc]
  have hn := S.tensor.map (Prod.mkHom (f ≫ phi) (𝟙 P')) ≫=
    ambientEvaluation_naturality S P Q P' Q' g h
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using hn

private def completedTensorUnitNat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    (pullbackTensorCalculus l E W).integralClosed.tensor ⟶ integralCompletedTensor l E W :=
  (Functor.rightUnitor _).inv ≫
    Functor.whiskerLeft _ (pullbackTensorCalculus l E W).adjunction.unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (pullbackTensorCalculus l E W).reductionTensor.hom
      (coefficientSequenceLimit l E W) ≫
    (pullbackTensorIntegralTensorModel l E W).inv

private theorem completedTensorUnit_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (M N M' N' : DerivedCategory (integralTowerModules l E W))
    (f : M ⟶ M') (g : N ⟶ N') :
    (pullbackTensorCalculus l E W).integralClosed.tensor.map (Prod.mkHom f g) ≫
        podCompletedTensorUnit l E W M' N' =
      podCompletedTensorUnit l E W M N ≫
        (integralCompletedTensor l E W).map (Prod.mkHom f g) := by
  let := (pullbackTensorCalculus l E W).integralClosed.monoidal
  simpa [completedTensorUnitNat, podCompletedTensorUnit,
    CoefficientClosedStructure.tensor, Category.assoc] using
    (completedTensorUnitNat l E W).naturality (Prod.mkHom f g)

private theorem integralTranspose_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (f : (constructibleIntegralTensor l E W).obj (L, P.obj.1.unop) ⟶ P.obj.2) :
    ((podIntegralClosed l E W).transpose L P f).hom =
      (pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫ f.hom) := by
  exact eq_of_heq ((podIntegralClosed_existsUnique l E W).exists.choose_spec L P f)

private theorem integralInverseTranspose_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L : sfIntegralConstructibleCategory l E W)
    (P : (constructibleIntegralHomPairs l E W).FullSubcategory)
    (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom =
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom := by
  apply ((pullbackTensorCalculus l E W).integralClosed.transpose _ _ _).injective
  rw [← integralTranspose_normalization, AddEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]

private theorem integralInverseTranspose_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L L' : sfIntegralConstructibleCategory l E W)
    (P P' : (constructibleIntegralHomPairs l E W).FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ (constructibleIntegralHom l E W).obj P) :
    ((podIntegralClosed l E W).transpose L' P').symm
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map g) =
      (constructibleIntegralTensor l E W).map (Prod.mkHom f g.hom.1.unop) ≫
        ((podIntegralClosed l E W).transpose L P).symm phi ≫ g.hom.2 := by
  have h := ambientInverseTranspose_naturality
    (pullbackTensorCalculus l E W).integralClosed L.obj L'.obj
      P.obj.1.unop.obj P.obj.2.obj P'.obj.1.unop.obj P'.obj.2.obj
      f.hom g.hom.1.unop.hom g.hom.2.hom phi.hom
  apply ((podIntegralClosed l E W).transpose L' P').injective
  apply ObjectProperty.hom_ext
  rw [integralTranspose_normalization, integralTranspose_normalization]
  change _ = (pullbackTensorCalculus l E W).integralClosed.transpose _ _ _
    (podCompletedTensorUnit l E W _ _ ≫
      ((integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
        (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom))
  have hu := integralInverseTranspose_normalization l E W L P phi
  have hn := completedTensorUnit_naturality l E W L'.obj P'.obj.1.unop.obj
    L.obj P.obj.1.unop.obj f.hom g.hom.1.unop.hom
  have heq : podCompletedTensorUnit l E W L'.obj P'.obj.1.unop.obj ≫
      (integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
      (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom =
      (pullbackTensorCalculus l E W).integralClosed.tensor.map
        (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
      ((pullbackTensorCalculus l E W).integralClosed.transpose L.obj P.obj.1.unop.obj
        P.obj.2.obj).symm phi.hom ≫ g.hom.2.hom := by
    calc
      _ = (pullbackTensorCalculus l E W).integralClosed.tensor.map
          (Prod.mkHom f.hom g.hom.1.unop.hom) ≫
          (podCompletedTensorUnit l E W L.obj P.obj.1.unop.obj ≫
          (((podIntegralClosed l E W).transpose L P).symm phi).hom) ≫ g.hom.2.hom := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦ k ≫
                (((podIntegralClosed l E W).transpose L P).symm phi).hom ≫ g.hom.2.hom)
                  hn.symm
      _ = _ := by rw [hu]
  exact congrArg ((pullbackTensorCalculus l E W).integralClosed.transpose
    L'.obj P'.obj.1.unop.obj P'.obj.2.obj)
      ((integralInverseTranspose_normalization l E W L' P'
        (f ≫ phi ≫ (constructibleIntegralHom l E W).map g)).trans (h.trans heq.symm))

private def completedBraidingNat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u}) :
    integralCompletedTensor l E W ≅
      pullbackTensorSwap _ ⋙ integralCompletedTensor l E W :=
  (pullbackTensorIntegralTensorModel l E W) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        ((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction)
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel))
      (coefficientSequenceLimit l E W) ≪≫
    Functor.isoWhiskerLeft (pullbackTensorSwap _)
      (pullbackTensorIntegralTensorModel l E W).symm

private theorem completedBraiding_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorIntegralBraiding l E W M N).hom.hom =
      (completedBraidingNat l E W).hom.app (M.obj, N.obj) := by
  let e : (constructibleIntegralTensor l E W).obj (M, N) ≅
      (constructibleIntegralTensor l E W).obj (N, M) :=
    ObjectProperty.isoMk _ ((completedBraidingNat l E W).app (M.obj, N.obj))
  have he : (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        (pullbackTensorIntegralReductionTensor l E W N M).hom =
      (pullbackTensorIntegralReductionTensor l E W M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj) := by
    dsimp only [e, completedBraidingNat, ObjectProperty.isoMk, ObjectProperty.homMk,
      pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.mapIso_hom, asIso_hom]
    simp only [Functor.map_comp, Category.assoc]
    erw [← Category.assoc
      ((pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).inv.app (N.obj, M.obj)))
      ((pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).hom.app (N.obj, M.obj))),
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    exact congrArg (fun k ↦
      (pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).hom.app (M.obj, N.obj)) ≫ k)
      ((pullbackTensorCalculus l E W).adjunction.counit.naturality _)
  have h := (pullbackTensorIntegralBraiding_existsUnique l E W M N).unique
    ((pullbackTensorIntegralBraiding_existsUnique l E W M N).exists.choose_spec) he
  exact congrArg (fun i ↦ i.hom.hom) h

private theorem integralBraiding_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M M' N N' : sfIntegralConstructibleCategory l E W) (f : M ⟶ M') (g : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom f g) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom g f) := by
  apply ObjectProperty.hom_ext
  change (integralCompletedTensor l E W).map (Prod.mkHom f.hom g.hom) ≫ _ =
    _ ≫ (integralCompletedTensor l E W).map (Prod.mkHom g.hom f.hom)
  rw [completedBraiding_normalization, completedBraiding_normalization]
  exact (completedBraidingNat l E W).hom.naturality (Prod.mkHom f.hom g.hom)

end WeilConjectures
