/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
import WeilConjectures.SmoothPurity.Supporting.Scalar.SystemScalarTensorAssociatorChain
import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus

/-! # Scalar extension preserves the associator of coherent systems

The derived scalar extension of coherent coefficient systems, with its normalized tensor
comparison `derivedSigma`, is compatible with the associators of the derived tensor products.
Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

section Helpers
open MonoidalCategory

/-- The selected calculus retains the system normalization from its resolution model.
Source: Stacks 07A4 and 0941 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem pullbackTensor_systemTensorCoherence (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _
      (pullbackTensorCalculus l E W).systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel β) := by
  unfold pullbackTensorCalculus
  exact (coefficientDerivedSystemEvaluationCalculus l E W).choose_spec.some.systemTensorCoherence

/-- Total tensors of flat-term K-flat complexes are again flat-term K-flat.
Source: Stacks 06YS and 07A2 (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem total_good (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) (X Y : ScalarExtensionTower.Complex l E W)
    (hX : ScalarExtensionTower.Good l E W X) (hY : ScalarExtensionTower.Good l E W Y) :
    ScalarExtensionTower.Good l E W ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W)).obj (X, Y)) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (coefficientSequenceCommRingSheaf l E W) X Y hX.1 hY.1 hX.2 hY.2
  exact ⟨h.1, h.2.1⟩

/-- A natural localization comparison transports a pasted chain-map square.
Source: naturality and functoriality in Stacks 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem localization_comparison_paste
    {C B D A : Type*} [Category C] [Category B] [Category D] [Category A]
    (F : C ⥤ B) (G : D ⥤ A) (U : B ⥤ A) (V : C ⥤ D)
    (e : F ⋙ U ⟶ V ⋙ G) {P Q : C} {R S R' S' : D}
    (a : P ⟶ Q) (b : V.obj Q ⟶ R) (c : R ⟶ S)
    (d : V.obj P ⟶ R') (j : R' ⟶ S') (a' : S' ⟶ S)
    (h : V.map a ≫ b ≫ c = d ≫ j ≫ a') :
    U.map (F.map a) ≫ (e.app Q ≫ G.map b ≫ G.map c) =
      (e.app P ≫ G.map d ≫ G.map j) ≫ G.map a' := by
  have he := e.naturality a
  dsimp only [Functor.comp_map] at he
  simp only [← Category.assoc]
  rw [he]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ e.app P ≫ G.map f) h

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem left_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ X ⊗ Y) (j : W ⟶ V ⊗ Z)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ X' ⊗ Y') (j' : W' ⟶ V' ⊗ Z')
    (hi : F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ) = eW ≫ j') :
    F.map (j ≫ (i ▷ Z)) ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX ⊗ₘ eY) ⊗ₘ eZ) =
      eW ≫ j' ≫ (i' ▷ Z') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (V, Z)) (Y := (X ⊗ Y, Z)) (i, 𝟙 Z)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, tensorHom_id] at hn
  calc
    _ = F.map j ≫ μ.hom.app (V, Z) ≫
        ((F.map i ≫ μ.hom.app (X, Y) ≫ (eX ⊗ₘ eY)) ⊗ₘ eZ) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (V, Z) ≫ ((eV ≫ i') ⊗ₘ eZ) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (V, Z) ≫ (eV ⊗ₘ eZ)) ≫ (i' ▷ Z') := by
      simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem right_square {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (i : V ⟶ Y ⊗ Z) (j : W ⟶ X ⊗ V)
    (eX : F.obj X ⟶ X') (eY : F.obj Y ⟶ Y') (eZ : F.obj Z ⟶ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (i' : V' ⟶ Y' ⊗ Z') (j' : W' ⟶ X' ⊗ V')
    (hi : F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ) = eV ≫ i')
    (hj : F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV) = eW ≫ j') :
    F.map (j ≫ (X ◁ i)) ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX ⊗ₘ (eY ⊗ₘ eZ)) =
      eW ≫ j' ≫ (X' ◁ i') := by
  dsimp only [Functor.comp_obj, Functor.prod_obj] at *
  have hn := μ.hom.naturality (X := (X, V)) (Y := (X, Y ⊗ Z)) (𝟙 X, i)
  simp only [Functor.comp_map, Functor.prod_map, tensor_map, F.map_id, id_tensorHom] at hn
  calc
    _ = F.map j ≫ μ.hom.app (X, V) ≫
        (eX ⊗ₘ (F.map i ≫ μ.hom.app (Y, Z) ≫ (eY ⊗ₘ eZ))) := by
      simp only [F.map_comp, Category.assoc]
      rw [reassoc_of% hn]
      simp only [← id_tensorHom, tensorHom_comp_tensorHom,
        Category.id_comp]
      erw [Category.id_comp]
    _ = F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ (eV ≫ i')) := by rw [hi]
    _ = (F.map j ≫ μ.hom.app (X, V) ≫ (eX ⊗ₘ eV)) ≫ (X' ◁ i') := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.assoc]
    _ = _ := by rw [hj]; simp only [Category.assoc]

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem associativity_transport
    {B : Type*} [Category B] [MonoidalCategory B]
    {A : Type*} [Category A] [MonoidalCategory A]
    (F : B ⥤ A)
    (μ : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    {X Y Z V W : B} {X' Y' Z' V' W' : A}
    (l : V ≅ (X ⊗ Y) ⊗ Z) (r : W ≅ X ⊗ (Y ⊗ Z)) (a : V ⟶ W)
    (l' : V' ⟶ (X' ⊗ Y') ⊗ Z') (r' : W' ⟶ X' ⊗ (Y' ⊗ Z')) (a' : V' ⟶ W')
    (eX : F.obj X ≅ X') (eY : F.obj Y ≅ Y') (eZ : F.obj Z ≅ Z')
    (eV : F.obj V ⟶ V') (eW : F.obj W ⟶ W')
    (hB : l.hom ≫ (α_ X Y Z).hom = a ≫ r.hom)
    (hA : l' ≫ (α_ X' Y' Z').hom = a' ≫ r')
    (hL : F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
      (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) = eV ≫ l')
    (hR : F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
      (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) = eW ≫ r')
    (hC : F.map a ≫ eW = eV ≫ a') :
    F.map (α_ X Y Z).hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) =
      μ.hom.app (X ⊗ Y, Z) ≫ (μ.hom.app (X, Y) ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  apply (cancel_epi (F.map l.hom)).1
  apply (cancel_mono (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom))).1
  calc
    _ = F.map a ≫ F.map r.hom ≫ μ.hom.app (X, Y ⊗ Z) ≫
        (F.obj X ◁ μ.hom.app (Y, Z)) ≫ (eX.hom ⊗ₘ (eY.hom ⊗ₘ eZ.hom)) := by
      rw [← F.map_comp_assoc, hB, F.map_comp]
      simp only [Category.assoc]
    _ = F.map a ≫ eW ≫ r' := by rw [hR]
    _ = eV ≫ a' ≫ r' := by rw [reassoc_of% hC]
    _ = eV ≫ l' ≫ (α_ X' Y' Z').hom := by rw [hA]
    _ = F.map l.hom ≫ μ.hom.app (X ⊗ Y, Z) ≫
        (μ.hom.app (X, Y) ▷ F.obj Z) ≫ ((eX.hom ⊗ₘ eY.hom) ⊗ₘ eZ.hom) ≫
          (α_ X' Y' Z').hom := by rw [reassoc_of% hL]
    _ = _ := by
      erw [associator_naturality]
      simp only [Category.assoc]
      rfl

/-- Natural transformations out of a functor of three variables agree once they agree on
triples of objects from a resolving class.
Source: naturality (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private theorem tripleNatTrans_ext_resolving
    {B : Type*} [Category B] {D : Type*} [Category D]
    {E : Type*} [Category E] (q : B ⥤ D) (P : ObjectProperty B)
    (res : ∀ X : D, ∃ Y : B, P Y ∧ Nonempty (q.obj Y ≅ X))
    {F G : D × D × D ⥤ E} (a b : F ⟶ G)
    (h : ∀ U V W : B, P U → P V → P W →
      a.app (q.obj U, q.obj V, q.obj W) = b.app (q.obj U, q.obj V, q.obj W)) :
    a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨U, hU, ⟨eU⟩⟩ := res X.1
  obtain ⟨V, hV, ⟨eV⟩⟩ := res X.2.1
  obtain ⟨W, hW, ⟨eW⟩⟩ := res X.2.2
  let e := Iso.prod eU (Iso.prod eV eW)
  apply (cancel_epi (F.map e.hom)).1
  rw [a.naturality, b.naturality, h U V W hU hV hW]

section Paths
variable {D : Type*} [Category D] [MonoidalCategory D]
  {E : Type*} [Category E] [MonoidalCategory E]
  (F : D ⥤ E) (μ : tensor D ⋙ F ≅ (F.prod F) ⋙ tensor E)

/-- The left side of the associativity square of a tensor comparison, as a transformation.
Source: naturality (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private def assocLeftPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E :=
  Functor.whiskerRight (associatorNatIso D).hom F ≫
    Functor.whiskerLeft ((𝟭 D).prod (tensor D)) μ.hom ≫
      Functor.whiskerRight (NatTrans.prod (𝟙 F) μ.hom) (tensor E)

/-- The right side of the associativity square of a tensor comparison, as a transformation.
Source: naturality (blueprint: lem-pur-derived-pullback-tensor-constraints). -/
private def assocRightPath :
    leftAssocTensor D ⋙ F ⟶ (F.prod (F.prod F)) ⋙ rightAssocTensor E := by
  let p₁ := CategoryTheory.Prod.fst D (D × D)
  let p₂ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.fst D D
  let p₃ := CategoryTheory.Prod.snd D (D × D) ⋙ CategoryTheory.Prod.snd D D
  let p₁₂ := p₁.prod' p₂
  exact Functor.whiskerLeft ((p₁₂ ⋙ tensor D).prod' p₃) μ.hom ≫
    Functor.whiskerRight
      (NatTrans.prod' (Functor.whiskerLeft p₁₂ μ.hom) (𝟙 (p₃ ⋙ F))) (tensor E) ≫
    Functor.whiskerLeft (F.prod (F.prod F)) (associatorNatIso E).hom

end Paths

end Helpers

section Representatives
attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel coefficientTotalTensor
  derivedInternalHomOfUniverses
attribute [local implicit_reducible] integralComparisonDerivedSequenceScalar
  ScalarExtensionTower.tensor Functor.mapHomologicalComplex CoefficientClosedStructure.tensor
  coefficientSequenceHasDerived

open MonoidalCategory ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

set_option maxHeartbeats 800000 in
-- Elaborating the four tensor-model normalization squares uses extra heartbeats.
/-- The scalar tensorator is compatible with the associators on three good representatives.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: the system associators are the localizations of the strict reassociations with the
fixed tensor models; the scalar tensorator is the localization of the strict `sigma` with the
same tensor models and the scalar counits. The strict square commutes on pure triples. -/
private theorem associator_representatives (P Q N : Complex l E W)
    (hP : Good l E W P) (hQ : Good l E W Q) (hN : Good l E W N) :
    let M₁ := DerivedCategory.Q.obj P
    let M₂ := DerivedCategory.Q.obj Q
    let M₃ := DerivedCategory.Q.obj N
    (integralComparisonDerivedSequenceScalar l E L ι W).map
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M₁ M₂ M₃).hom ≫
      (derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        (M₁, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (M₂, M₃)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj M₁))
          ((derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (M₂, M₃))) =
    (derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M₁, M₂), M₃) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom
          ((derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (M₁, M₂))
          (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj M₃))) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M₁)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M₂)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M₃)).hom := by
  let J := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf l E W
  let RL := coefficientSequenceCommRingSheaf l L W
  let C := scalar l E L ι W
  let δ := integralComparisonSequenceScalarModel l E L ι W
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let SE := pullbackTensorCalculus l E W
  let SL := pullbackTensorCalculus l L W
  let SB := SE.systemClosed
  let TB := SE.systemTensorModel
  let SA := SL.systemClosed
  let TA := SL.systemTensorModel
  let μ := derivedSigma l E L ι W SE SL
  let κ := (comparisons l).sigma E L ι W
  obtain ⟨βB, ⟨cB⟩⟩ := pullbackTensor_systemTensorCoherence l E W
  obtain ⟨βA, ⟨cA⟩⟩ := pullbackTensor_systemTensorCoherence l L W
  let := SB.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l E W) :=
    SB.monoidal.toMonoidalCategoryStruct
  let := SA.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l L W) :=
    SA.monoidal.toMonoidalCategoryStruct
  change H.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj N)).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (𝟙 (H.obj (DerivedCategory.Q.obj P)) ⊗ₘ
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
    μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⊗ₘ
        𝟙 (H.obj (DerivedCategory.Q.obj N))) ≫
      (α_ (H.obj (DerivedCategory.Q.obj P)) (H.obj (DerivedCategory.Q.obj Q))
        (H.obj (DerivedCategory.Q.obj N))).hom
  erw [id_tensorHom, tensorHom_id]
  have hα := (derivedSigma_existsUnique l E L ι W SE SL).exists.choose_spec
  change DerivedSigmaModel l E L ι W SE SL μ at hα
  unfold DerivedSigmaModel at hα
  let B := coefficientTotalTensor.{u, u + 1, u} J RE
  let A := coefficientTotalTensor.{u, u + 1, u} J RL
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := total_good l E W P Q hP hQ
  have hQN := total_good l E W Q N hQ hN
  obtain ⟨hUP, hUQ, hmPQ⟩ := hα P Q hP hQ
  obtain ⟨_, hUN, hmQN⟩ := hα Q N hQ hN
  obtain ⟨hUPQ, _, hmL⟩ := hα PQ N hPQ hN
  obtain ⟨_, hUQN, hmR⟩ := hα P QN hP hQN
  have : IsIso (δ.ε.app P) := δ.computes P hP.1
  have : IsIso (δ.ε.app Q) := δ.computes Q hQ.1
  have : IsIso (δ.ε.app N) := δ.computes N hN.1
  have hAPQ := coefficientTotalTensor_isKFlat.{u, u + 1, u} J RL (C.obj P) (C.obj Q)
    hUP.1 hUQ.1
  have hAQN := coefficientTotalTensor_isKFlat.{u, u + 1, u} J RL (C.obj Q) (C.obj N)
    hUQ.1 hUN.1
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP.1 hQ.1 hN.1
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (C.obj P) (C.obj Q) (C.obj N)
    hUP.1 hUQ.1 hUN.1
  have hc := scalarSigma_cochain_associativity l E L ι W P Q N aB aA haB haA
  rw [show cB.tensorIso PQ N (Or.inr hN.1) = TB.iso J RE SB PQ N hPQ.1 hN.1 from
      cB.tensorIso_both PQ N hPQ.1 hN.1,
    cB.tensorIso_both P QN hP.1 hQN.1] at heB
  rw [show cA.tensorIso (A.obj (C.obj P, C.obj Q)) (C.obj N) (Or.inr hUN.1) =
      TA.iso J RL SA _ _ hAPQ hUN.1 from cA.tensorIso_both _ _ hAPQ hUN.1,
    cA.tensorIso_both (C.obj P) (A.obj (C.obj Q, C.obj N)) hUP.1 hAQN] at heA
  let bPQ := TB.iso J RE SB P Q hP.1 hQ.1
  let bQN := TB.iso J RE SB Q N hQ.1 hN.1
  let bL := TB.iso J RE SB PQ N hPQ.1 hN.1
  let bR := TB.iso J RE SB P QN hP.1 hQN.1
  let aPQ := TA.iso J RL SA (C.obj P) (C.obj Q) hUP.1 hUQ.1
  let aQN := TA.iso J RL SA (C.obj Q) (C.obj N) hUQ.1 hUN.1
  let aL := TA.iso J RL SA (A.obj (C.obj P, C.obj Q)) (C.obj N) hAPQ hUN.1
  let aR := TA.iso J RL SA (C.obj P) (A.obj (C.obj Q, C.obj N)) hUP.1 hAQN
  let aL₀ := TA.iso J RL SA (C.obj PQ) (C.obj N) hUPQ.1 hUN.1
  let aR₀ := TA.iso J RL SA (C.obj P) (C.obj QN) hUP.1 hUQN.1
  let lB := bL ≪≫ whiskerRightIso bPQ (DerivedCategory.Q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (DerivedCategory.Q.obj (C.obj N))
  let rA := aR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj (C.obj P)) aQN
  let tPQ : DerivedCategory.Q.obj (C.obj PQ) ⟶
      DerivedCategory.Q.obj (A.obj (C.obj P, C.obj Q)) :=
    DerivedCategory.Q.map (κ.hom.app (P, Q))
  let tQN : DerivedCategory.Q.obj (C.obj QN) ⟶
      DerivedCategory.Q.obj (A.obj (C.obj Q, C.obj N)) :=
    DerivedCategory.Q.map (κ.hom.app (Q, N))
  let tL : DerivedCategory.Q.obj (C.obj (B.obj (PQ, N))) ⟶
      DerivedCategory.Q.obj (A.obj (C.obj PQ, C.obj N)) :=
    DerivedCategory.Q.map (κ.hom.app (PQ, N))
  let tR : DerivedCategory.Q.obj (C.obj (B.obj (P, QN))) ⟶
      DerivedCategory.Q.obj (A.obj (C.obj P, C.obj QN)) :=
    DerivedCategory.Q.map (κ.hom.app (P, QN))
  let eL := δ.ε.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (C.obj PQ, C.obj N))
      (Y := (A.obj (C.obj P, C.obj Q), C.obj N))
      (κ.hom.app (P, Q), 𝟙 (C.obj N)))
  let eR := δ.ε.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (C.obj P, C.obj QN))
      (Y := (C.obj P, A.obj (C.obj Q, C.obj N)))
      (𝟙 (C.obj P), κ.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    change (bL.hom ≫ (bPQ.hom ▷ DerivedCategory.Q.obj N)) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map aB.hom ≫ (bR.hom ≫ (DerivedCategory.Q.obj P ◁ bQN.hom))
    simpa only [bL, bR, bPQ, bQN, CoefficientClosedStructure.tensor, tensor_map,
      tensorHom_id, id_tensorHom, Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (C.obj P))
        (DerivedCategory.Q.obj (C.obj Q)) (DerivedCategory.Q.obj (C.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    change (aL.hom ≫ (aPQ.hom ▷ DerivedCategory.Q.obj (C.obj N))) ≫
        (α_ (DerivedCategory.Q.obj (C.obj P)) (DerivedCategory.Q.obj (C.obj Q))
          (DerivedCategory.Q.obj (C.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ (aR.hom ≫ (DerivedCategory.Q.obj (C.obj P) ◁ aQN.hom))
    simpa only [aL, aR, aPQ, aQN, CoefficientClosedStructure.tensor, tensor_map,
      tensorHom_id, id_tensorHom, Category.assoc] using heA
  change H.map bPQ.hom ≫ μ.hom.app (_, _) ≫
    ((δ.ε.app P) ⊗ₘ (δ.ε.app Q)) = δ.ε.app _ ≫ tPQ ≫ aPQ.hom at hmPQ
  change H.map bQN.hom ≫ μ.hom.app (_, _) ≫
    ((δ.ε.app Q) ⊗ₘ (δ.ε.app N)) = δ.ε.app _ ≫ tQN ≫ aQN.hom at hmQN
  change H.map bL.hom ≫ μ.hom.app (_, _) ≫
    ((δ.ε.app PQ) ⊗ₘ (δ.ε.app N)) = δ.ε.app _ ≫ tL ≫ aL₀.hom at hmL
  change H.map bR.hom ≫ μ.hom.app (_, _) ≫
    ((δ.ε.app P) ⊗ₘ (δ.ε.app QN)) = δ.ε.app _ ≫ tR ≫ aR₀.hom at hmR
  have hnL := TA.comparison.hom.naturality
    (X := (⟨C.obj PQ, hUPQ.1⟩, ⟨C.obj N, hUN.1⟩))
    (Y := (⟨A.obj (C.obj P, C.obj Q), hAPQ⟩, ⟨C.obj N, hUN.1⟩))
    (ObjectProperty.homMk (κ.hom.app (P, Q)), ObjectProperty.homMk (𝟙 (C.obj N)))
  change DerivedCategory.Q.map (A.map (κ.hom.app (P, Q), 𝟙 (C.obj N))) ≫ aL.hom =
    aL₀.hom ≫ SA.tensor.map
      (X := (DerivedCategory.Q.obj (C.obj PQ), DerivedCategory.Q.obj (C.obj N)))
      (Y := (DerivedCategory.Q.obj (A.obj (C.obj P, C.obj Q)),
        DerivedCategory.Q.obj (C.obj N)))
      (DerivedCategory.Q.map (κ.hom.app (P, Q)), DerivedCategory.Q.map (𝟙 (C.obj N))) at hnL
  have hnR := TA.comparison.hom.naturality
    (X := (⟨C.obj P, hUP.1⟩, ⟨C.obj QN, hUQN.1⟩))
    (Y := (⟨C.obj P, hUP.1⟩, ⟨A.obj (C.obj Q, C.obj N), hAQN⟩))
    (ObjectProperty.homMk (𝟙 (C.obj P)), ObjectProperty.homMk (κ.hom.app (Q, N)))
  change DerivedCategory.Q.map (A.map (𝟙 (C.obj P), κ.hom.app (Q, N))) ≫ aR.hom =
    aR₀.hom ≫ SA.tensor.map
      (X := (DerivedCategory.Q.obj (C.obj P), DerivedCategory.Q.obj (C.obj QN)))
      (Y := (DerivedCategory.Q.obj (C.obj P),
        DerivedCategory.Q.obj (A.obj (C.obj Q, C.obj N))))
      (DerivedCategory.Q.map (𝟙 (C.obj P)), DerivedCategory.Q.map (κ.hom.app (Q, N))) at hnR
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnL
  erw [tensorHom_id] at hnL
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnR
  erw [id_tensorHom] at hnR
  have hL₀ := left_square
    H μ bPQ.hom bL.hom
    (δ.ε.app P) (δ.ε.app Q) (δ.ε.app N) (δ.ε.app PQ)
    (δ.ε.app (B.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := right_square
    H μ bQN.hom bR.hom
    (δ.ε.app P) (δ.ε.app Q) (δ.ε.app N) (δ.ε.app QN)
    (δ.ε.app (B.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : H.map lB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q,
        DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        H.obj (DerivedCategory.Q.obj N)) ≫
      (((δ.ε.app P) ⊗ₘ (δ.ε.app Q)) ⊗ₘ (δ.ε.app N)) = eL ≫ lA.hom := by
    calc
      _ = δ.ε.app (B.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ DerivedCategory.Q.obj (C.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
  have hR : H.map rB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (H.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      ((δ.ε.app P) ⊗ₘ ((δ.ε.app Q) ⊗ₘ (δ.ε.app N))) = eR ≫ rA.hom := by
    calc
      _ = δ.ε.app (B.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (DerivedCategory.Q.obj (C.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  have hC := localization_comparison_paste DerivedCategory.Q DerivedCategory.Q
    H C δ.ε _ _ _ _ _ _ hc
  refine associativity_transport
    H μ lB rB (DerivedCategory.Q.map aB.hom)
    lA.hom rA.hom (DerivedCategory.Q.map aA.hom) (asIso (δ.ε.app P)) (asIso (δ.ε.app Q))
    (asIso (δ.ε.app N)) eL eR ?_ ?_ ?_ ?_ ?_
  · exact hB
  · exact hA
  · exact hL
  · exact hR
  · exact hC


/-- The normalized whole-system scalar tensorator is compatible with the associators.
Source: Stacks 07A4 and 0FPT (blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: on flat-term K-flat representatives, the associators descend the strict reassociation
of total-complex summands and the tensorator descends the strict scalar comparison `sigma`.
On a homogeneous local tensor `x ⊗ y ⊗ z` both strict routes give `x ⊗ y ⊗ z` with the
scalar `1`. These generators span the sheafified total tensors, so the strict chain maps agree;
localize, cancel the tensor models and scalar counits, and use naturality to pass from
representatives to arbitrary system objects. -/
theorem systemScalarTensorAssociator
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Field L]
    [Algebra (Padic l) E] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N P : coefficientSequenceDerived l E W) :
    (integralComparisonDerivedSequenceScalar l E L ι W).map
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj M))
          ((ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (N, P))) =
    (ScalarExtensionTower.derivedSigma l E L ι W
        (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom
          ((ScalarExtensionTower.derivedSigma l E L ι W
            (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)).hom.app (M, N))
          (𝟙 ((integralComparisonDerivedSequenceScalar l E L ι W).obj P))) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj M)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj N)
        ((integralComparisonDerivedSequenceScalar l E L ι W).obj P)).hom := by
  let : MonoidalCategory (coefficientSequenceDerived l E W) :=
    (pullbackTensorCalculus l E W).systemClosed.monoidal
  let : MonoidalCategory (coefficientSequenceDerived l L W) :=
    (pullbackTensorCalculus l L W).systemClosed.monoidal
  let F := integralComparisonDerivedSequenceScalar l E L ι W
  let μ := derivedSigma l E L ι W (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  have res (X : coefficientSequenceDerived l E W) :
      ∃ P : Complex l E W, Good l E W P ∧ Nonempty (DerivedCategory.Q.obj P ≅ X) := by
    let q := DerivedCategory.Q (C := coefficientSequenceModules l E W)
    obtain ⟨P, f, hP, hflat, hf, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := coefficientSequenceCommRingSheaf l E W) (q.objPreimage X)
    have : QuasiIso f := hf
    refine ⟨P, ⟨hP, fun n ↦ ?_⟩, ⟨asIso (q.map f) ≪≫ q.objObjPreimageIso X⟩⟩
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso
        (coefficientSequenceCommRingSheaf l E W) (P.X n)).symm (hflat n)
  have hab : assocLeftPath F μ = assocRightPath F μ :=
    tripleNatTrans_ext_resolving DerivedCategory.Q (Good l E W) res _ _ (by
      intro A B C hA hB hC
      exact associator_representatives l E L ι W A B C hA hB hC)
  exact NatTrans.congr_app hab (M, N, P)

end Representatives

end WeilConjectures
