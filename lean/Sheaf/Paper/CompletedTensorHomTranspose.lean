/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.DerivedAutomorphismHomEvaluation
public import Sheaf.Paper.DirectImagesConstructible

import Sheaf.Paper.CompletedTensorScalarLinearity
import Sheaf.Paper.NormalizedRationalEvaluationNaturality
import Sheaf.Paper.LocalizedTensorBraidingNaturality

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

/-- The three equations meant by evaluation transposition, naturality in all three
variables, and signed symmetry compatibility. Here S is the already normalized
Hom-first closed data and beta is the recorded signed tensor symmetry.
Source: blueprint equivariance proof paragraph 2; Stacks 08J9
(blueprint: lem-coef-completed-tensor-hom-transpose). -/
structure CoefficientTransposeLaws {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (tau : ∀ (L : A) (P : J.FullSubcategory),
      (L ⟶ H.obj P) → (T.obj (P.obj.1.unop, L) ⟶ P.obj.2)) : Prop where
  /-- Evaluation with the argument first, as in the node's displayed formula. -/
  evaluation : ∀ L P phi,
    tau L P phi = T.map (Prod.mkHom (𝟙 P.obj.1.unop) phi) ≫
      (beta P.obj.1.unop (H.obj P)).hom ≫ S.evaluation P
  /-- One equation includes contravariance in P,L and covariance in Q. -/
  naturality : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ H.obj P),
    tau L' P' (f ≫ phi ≫ H.map g) =
      T.map (Prod.mkHom g.hom.1.unop f) ≫ tau L P phi ≫ g.hom.2
  /-- It is the Hom-first transpose precomposed with the canonical Koszul symmetry. -/
  symmetry : ∀ L P phi,
    tau L P phi = (beta P.obj.1.unop L).hom ≫ (S.transpose L P).symm phi

private def signedTranspose {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (L : A) (P : J.FullSubcategory) :
    (L ⟶ H.obj P) ≃+ (T.obj (P.obj.1.unop, L) ⟶ P.obj.2) where
  toFun phi := (beta P.obj.1.unop L).hom ≫ (S.transpose L P).symm phi
  invFun h := S.transpose L P ((beta P.obj.1.unop L).inv ≫ h)
  left_inv phi := by
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      AddEquiv.apply_symm_apply]
  right_inv h := by
    simp only [AddEquiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  map_add' phi psi := by
    simp only [map_add, Preadditive.comp_add]

private theorem inverseTranspose_evaluation {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (L : A) (P : J.FullSubcategory) (phi : L ⟶ H.obj P) :
    (S.transpose L P).symm phi =
      T.map (Prod.mkHom phi (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [AddEquiv.apply_symm_apply, S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

private theorem signedTranspose_evaluation {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (L : A) (P : J.FullSubcategory) (phi : L ⟶ H.obj P) :
    signedTranspose S beta L P phi = T.map (Prod.mkHom (𝟙 _) phi) ≫
      (beta P.obj.1.unop (H.obj P)).hom ≫ S.evaluation P := by
  change (beta _ _).hom ≫ _ = _
  rw [inverseTranspose_evaluation, ← Category.assoc, ← hn]
  exact Category.assoc _ _ _

private theorem signedTranspose_naturality {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (hs : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
      (g : P ⟶ P') (phi : L ⟶ H.obj P),
      (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
        T.map (Prod.mkHom f g.hom.1.unop) ≫ (S.transpose L P).symm phi ≫ g.hom.2)
    (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L) (g : P ⟶ P')
    (phi : L ⟶ H.obj P) :
    signedTranspose S beta L' P' (f ≫ phi ≫ H.map g) =
      T.map (Prod.mkHom g.hom.1.unop f) ≫ signedTranspose S beta L P phi ≫ g.hom.2 := by
  change (beta _ _).hom ≫ _ = _
  rw [hs]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [signedTranspose, AddEquiv.coe_mk, Equiv.coe_fn_mk, Category.assoc]

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

private def signedLinearTranspose {R : Type*} [CommRing R]
    {A : Type a} [Category.{b} A] [Preadditive A] [Linear R A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hl : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N') (c : R),
      T.map (Prod.mkHom (c • f) g) = c • T.map (Prod.mkHom f g))
    (L : A) (P : J.FullSubcategory) :
    (L ⟶ H.obj P) ≃ₗ[R] (T.obj (P.obj.1.unop, L) ⟶ P.obj.2) :=
  { signedTranspose S beta L P with
    map_smul' := by
      intro c phi
      change (beta _ _).hom ≫ (S.transpose L P).symm (c • phi) =
        c • ((beta _ _).hom ≫ (S.transpose L P).symm phi)
      rw [inverseTranspose_evaluation, inverseTranspose_evaluation, hl,
        Linear.smul_comp, Linear.comp_smul] }

private theorem signedTranspose_laws {A : Type a} [Category.{b} A] [Preadditive A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (hs : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
      (g : P ⟶ P') (phi : L ⟶ H.obj P),
      (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
        T.map (Prod.mkHom f g.hom.1.unop) ≫ (S.transpose L P).symm phi ≫ g.hom.2) :
    CoefficientTransposeLaws S beta (fun L P phi ↦ signedTranspose S beta L P phi) := by
  exact ⟨signedTranspose_evaluation S beta hn,
    signedTranspose_naturality S beta hn hs, fun _ _ _ ↦ rfl⟩

private theorem integralTranspose_exists {R : Type*} [CommRing R]
    {A : Type a} [Category.{b} A] [Preadditive A] [Linear R A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hl : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N') (c : R),
      T.map (Prod.mkHom (c • f) g) = c • T.map (Prod.mkHom f g))
    (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (hs : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
      (g : P ⟶ P') (phi : L ⟶ H.obj P),
      (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
        T.map (Prod.mkHom f g.hom.1.unop) ≫ (S.transpose L P).symm phi ≫ g.hom.2) :
    ∃ tau : ∀ L P, (L ⟶ H.obj P) ≃ₗ[R] (T.obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws S beta (fun L P phi ↦ tau L P phi) := by
  exact ⟨signedLinearTranspose S beta hl, signedTranspose_laws S beta hn hs⟩

private theorem rationalTranspose_exists {R : Type*} [CommRing R]
    {A : Type a} [Category.{b} A] [Preadditive A] [Linear R A]
    {T : A × A ⥤ A} {J : ObjectProperty (Aᵒᵖ × A)} {H : J.FullSubcategory ⥤ A}
    (S : PodPartialClosed T J H) (beta : ∀ M N : A, T.obj (M, N) ≅ T.obj (N, M))
    (hl : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N') (c : R),
      T.map (Prod.mkHom (c • f) g) = c • T.map (Prod.mkHom f g))
    (hn : ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (beta M' N').hom =
        (beta M N).hom ≫ T.map (Prod.mkHom g f))
    (hs : ∀ (L L' : A) (P P' : J.FullSubcategory) (f : L' ⟶ L)
      (g : P ⟶ P') (phi : L ⟶ H.obj P),
      (S.transpose L' P').symm (f ≫ phi ≫ H.map g) =
        T.map (Prod.mkHom f g.hom.1.unop) ≫ (S.transpose L P).symm phi ≫ g.hom.2)
    {V : Type*} (v : V → R) :
    ∃ tau : ∀ L P, (L ⟶ H.obj P) ≃+ (T.obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws S beta (fun L P phi ↦ tau L P phi) ∧
      ∀ L P (phi : L ⟶ H.obj P) (c : V), tau L P (v c • phi) = v c • tau L P phi := by
  refine ⟨fun L P ↦ (signedLinearTranspose S beta hl L P).toAddEquiv,
    signedTranspose_laws S beta hn hs, ?_⟩
  intro L P phi c
  exact (signedLinearTranspose S beta hl L P).map_smul (v c) phi

private def TensorLinearFirst (R : Type*) [CommRing R]
    {A : Type a} [Category.{b} A] [Preadditive A] [Linear R A] (F : A × A ⥤ A) : Prop :=
  ∀ (M M' N N' : A) (f : M ⟶ M') (g : N ⟶ N') (c : R),
    F.map (Prod.mkHom (c • f) g) = c • F.map (Prod.mkHom f g)

private theorem bilinear_linearFirst {R : Type*} [CommRing R]
    {A : Type a} [Category.{b} A] [Preadditive A] [Linear R A]
    (F : A × A ⥤ A)
    (Q : ∀ M M' N N', ((M ⟶ M') →ₗ[R] (N ⟶ N') →ₗ[R]
      (F.obj (M, N) ⟶ F.obj (M', N'))) → Prop)
    (h : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[R] (N ⟶ N') →ₗ[R]
      (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧ Q M M' N N' b) :
    TensorLinearFirst R F := by
  intro M M' N N' f g c
  obtain ⟨b, hb, _⟩ := h M M' N N'
  rw [hb, hb, map_smul, LinearMap.smul_apply]

private theorem rationalTensor_linearFirst
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    TensorLinearFirst (Localization.Away (Padic.coefficientExtensionUniformizer l E))
      (rationalDerivedTensor l E W) := by
  exact bilinear_linearFirst
    (R := Localization.Away (Padic.coefficientExtensionUniformizer l E)) _ _
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.2

private theorem rationalInverseTranspose_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (L L' : sfRationalConstructibleCategory l E W)
    (P P' : (constructibleRationalHomPairs l E W).FullSubcategory) (f : L' ⟶ L)
    (g : P ⟶ P') (phi : L ⟶ (rationalDerivedInternalHom l E W).obj P) :
    ((podRationalClosed l E W).transpose L' P').symm
        (f ≫ phi ≫ (rationalDerivedInternalHom l E W).map g) =
      (rationalDerivedTensor l E W).map (Prod.mkHom f g.hom.1.unop) ≫
        ((podRationalClosed l E W).transpose L P).symm phi ≫ g.hom.2 := by
  rw [inverseTranspose_evaluation, inverseTranspose_evaluation]
  have hn := (rationalDerivedTensor l E W).map (Prod.mkHom (f ≫ phi) (𝟙 _)) ≫=
    normalizedRationalEvaluation_naturality l E W P P' g
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using hn

/-- Residue-field inverses transported from the fixed base field. Naming this
canonical expression avoids repeating its elaboration in the transpose statement.
Source: blueprint coefficient convention, equivariance proof paragraph 2
(blueprint: lem-coef-completed-tensor-hom-transpose). -/
@[instance_reducible] def coefficientTransposeUnits
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))] :
    ∀ x : X, Invertible (C.l : X.residueField x) :=
  fun x ↦ (by
    simpa using (finiteFieldDatumPrimeUnit D C.l C.different).map
      ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
        IsUnit (C.l : X.residueField x)).invertible

/-- Completed and raw rational transposition, with the precise evaluation formula,
all three naturalities and the signed tensor convention. The permitted pair P
bundles the node's objects P,Q and exactly its internal-Hom constructibility hypothesis.
Source: blueprint cor-coef-verdier-weil-equivariance, proof paragraph 2
(blueprint: lem-coef-completed-tensor-hom-transpose).

Proof (the four steps of the DAG):
1. On the completed-coefficient ringed site, identify global degree-zero derived
Hom with morphisms by lem-pur-rhom-global-sections. Internal-Hom currying gives
Hom(L,Hom(P,Q)) = Hom(L tensor P,Q). The model of def-coef-ringed-tensor-hom-model
identifies this with the evaluation counit, including its signed symmetry.
2. On simultaneous flat-term K-flat representatives, the balanced tensor comparison
sends (a tensor b) tensor r to (a tensor r) tensor (b tensor 1) at every quotient.
It commutes with quotient transitions. Thus the recorded completed tensor is the
quotient-tower completion of the ambient tensor, with its actual unit.
lem-weil-pbc-constant-completion-equivalence identifies that unit with Koszul
completion; lem-weil-pbc-ringed-koszul-completion-reflector gives the Hom bijection
into complete Q. Extend ambient evaluation uniquely along this unit.
lem-coef-derived-system-evaluation-calculus preserves this evaluation comparison.
Naturality of the unit proves that the extension of the ambient transpose is
exactly evaluation composed with 1 tensor phi.
3. Currying, global Hom and completion are natural and R-linear, so uniqueness
proves the stated three-variable equation. On degrees a,b the symmetry and
evaluation both introduce (-1)^(a*b). The normalized representative evaluation
and uniqueness through completion give the signed-symmetry equation.
4. Raw rationalization tensors the integral Hom groups and this R-linear
bijection with E. Its inverse tensors too. The operation formulas extend
bilinearly; hence evaluation, naturality and symmetry persist for every rational
arrow, including sums of pure tensors, with the displayed E scalar action.
No idempotent completion or lattice-preserving restriction is used. -/
theorem completedTensorHomTranspose
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra ℚ_[C.l] E] [FiniteDimensional ℚ_[C.l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    (∃ tau : ∀ (L : sfIntegralConstructibleCategory C.l E X)
        (P : (constructibleIntegralHomPairs C.l E X).FullSubcategory),
        (L ⟶ (constructibleIntegralHom C.l E X).obj P) ≃ₗ[
          Padic.coefficientExtensionIntegers C.l E]
          ((@constructibleIntegralTensor C.l _ E _ _ _ X
            (coefficientTransposeUnits D C X)).obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws
        (@podIntegralClosed C.l _ E _ _ _ X (coefficientTransposeUnits D C X))
        (@pullbackTensorIntegralBraiding C.l _ E _ _ _ X
          (coefficientTransposeUnits D C X))
        (fun L P phi ↦ tau L P phi)) ∧
    (∃ tau : ∀ (L : sfRationalConstructibleCategory C.l E X)
        (P : (constructibleRationalHomPairs C.l E X).FullSubcategory),
        (L ⟶ (rationalDerivedInternalHom C.l E X).obj P) ≃+
          ((@rationalDerivedTensor C.l _ E _ _ _ X
            (coefficientTransposeUnits D C X)).obj (P.obj.1.unop, L) ⟶ P.obj.2),
      CoefficientTransposeLaws
        (@podRationalClosed C.l _ E _ _ _ X (coefficientTransposeUnits D C X))
        (@pullbackTensorRationalBraiding C.l _ E _ _ _ X
          (coefficientTransposeUnits D C X))
        (fun L P phi ↦ tau L P phi) ∧
      ∀ L P (phi : L ⟶ (rationalDerivedInternalHom C.l E X).obj P) (c : E),
        tau L P ((sfRationalCoefficientEquiv C.l E).symm c • phi) =
          (sfRationalCoefficientEquiv C.l E).symm c • tau L P phi) := by
  let := coefficientTransposeUnits D C X
  constructor
  · exact integralTranspose_exists
      (R := Padic.coefficientExtensionIntegers C.l E)
      (T := constructibleIntegralTensor C.l E X)
      (J := constructibleIntegralHomPairs C.l E X)
      (H := constructibleIntegralHom C.l E X) (podIntegralClosed C.l E X)
      (pullbackTensorIntegralBraiding C.l E X) (completedTensor_map_smul_left C.l E X)
      (integralBraiding_naturality C.l E X) (integralInverseTranspose_naturality C.l E X)
  · exact rationalTranspose_exists
      (R := Localization.Away (Padic.coefficientExtensionUniformizer C.l E))
      (T := rationalDerivedTensor C.l E X)
      (J := constructibleRationalHomPairs C.l E X)
      (H := rationalDerivedInternalHom C.l E X) (podRationalClosed C.l E X)
      (pullbackTensorRationalBraiding C.l E X) (rationalTensor_linearFirst C.l E X)
      (fun M M' N N' f g ↦
        localizedTensorBraiding_naturality C.l E X (integralBraiding_naturality C.l E X)
          M M' N N' f g) (rationalInverseTranspose_naturality C.l E X)
      (sfRationalCoefficientEquiv C.l E).symm


end WeilConjectures
