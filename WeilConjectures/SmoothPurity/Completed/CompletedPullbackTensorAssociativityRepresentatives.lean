/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorCochainAssociativity

/-! # Associativity for coherent pullback tensor representatives

Source: Stacks 07A4, `lemma-pullback-tensor-product`, and 07A2,
`lemma-tensor-product-K-flat`.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] pullbackTensorCalculus
attribute [local implicit_reducible] pullbackTensorSequenceDerived
  pullbackTensorSystemComparison pullbackTensorSystemModel
  coefficientSequenceInternalHom coefficientSequenceHasDerived CoefficientClosedStructure.tensor
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory _root_.instCategoryDerivedCategory DerivedCategory.Q HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CochainComplex.IsKFlatIndependentCoefficients
  pullbackTensorSequenceInverse derivedInternalHomOfUniverses coefficientTotalTensor
  Functor.mapHomologicalComplex pullbackTensorSequenceCochain
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The selected calculus retains the system normalization from its resolution model.
Source: Stacks 07A4 and 0941
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem pullbackTensor_systemTensorCoherence (W : Scheme.{u}) :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _
      (pullbackTensorCalculus l E W).systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence.{u + 1, u, u}
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l E W)
        (pullbackTensorCalculus l E W).systemClosed
        (pullbackTensorCalculus l E W).systemTensorModel β) := by
  unfold pullbackTensorCalculus
  exact (coefficientDerivedSystemEvaluationCalculus l E W).choose_spec.some.systemTensorCoherence

/-- A natural localization comparison transports a pasted chain-map square.
Source: naturality and functoriality in Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
private theorem localization_comparison_paste
    {C B D A : Type*} [Category C] [Category B] [Category D] [Category A]
    (F : C ⥤ B) (G : D ⥤ A) (U : B ⥤ A) (V : C ⥤ D)
    (e : F ⋙ U ≅ V ⋙ G) {P Q : C} {R S R' S' : D}
    (a : P ⟶ Q) (b : V.obj Q ⟶ R) (c : R ⟶ S)
    (d : V.obj P ⟶ R') (j : R' ⟶ S') (a' : S' ⟶ S)
    (h : V.map a ≫ b ≫ c = d ≫ j ≫ a') :
    U.map (F.map a) ≫ (e.hom.app Q ≫ G.map b ≫ G.map c) =
      (e.hom.app P ≫ G.map d ≫ G.map j) ≫ G.map a' := by
  have he := e.hom.naturality a
  dsimp only [Functor.comp_map] at he
  simp only [← Category.assoc]
  rw [he]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ e.hom.app P ≫ G.map f) h

/-- Categorical pasting, from naturality and cancellation.
Source: Stacks 07A4
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
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
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
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
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives). -/
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

set_option maxHeartbeats 800000 in
set_option profiler true in
-- Elaborating the four tensor-model normalization squares uses extra heartbeats.
/-- Associativity on three localized coherent K-flat representatives.
Source: Stacks 07A4, total tensor construction; 07A2, K-flat tensor products.
(blueprint: lem-pur-completed-pullback-tensor-associativity-representatives).
Proof: total tensors of K-flat complexes are K-flat: reassociate an acyclic
test tensor and apply the two K-flat criteria. Apply the normalization of the
coherent comparison to (A,B), (B,C), (A tensor B,C) and (A,B tensor C), and
use preservation of K-flatness by the sequence inverse image. In every triple
degree both ordinary paths send the adjunction-unit image of (x tensor y)
tensor z to the tensor of the unit images of x, y and z, with parentheses on
the right. Naturality of the unit and the two normalized pure-tensor formulas
identify these sections. Reassociation introduces no permutation or extra sign
and commutes with all three signed differential terms. Tensor sheafification
and the total coproduct injections detect equality, so the chain maps agree.
Apply the derived quotient and insert the fixed tensor-model and exact-pullback
factorization isomorphisms. Their naturality cancels the intermediate maps;
the model associators identify the remaining reassociation maps with the
specified derived associators. This proves the equation on the displayed
representatives; extension to arbitrary derived objects is a separate step. -/
theorem completedPullbackTensor_associativity_representatives {X Y : Scheme.{u}}
    (f : X ⟶ Y) (A B C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) A)
    (hB : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) B)
    (hC : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := coefficientSequenceTopology (ProEt.topology Y))
      (R := coefficientSequenceCommRingSheaf l E Y) C) :
    let M := DerivedCategory.Q.obj A
    let N := DerivedCategory.Q.obj B
    let P := DerivedCategory.Q.obj C
    (pullbackTensorSequenceDerived l E f).map
      ((pullbackTensorCalculus l E Y).systemClosed.monoidal.associator M N P).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (M,(pullbackTensorCalculus l E Y).systemClosed.tensor.obj (N,P)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) ((pullbackTensorSystemComparison l E f).hom.app (N,P))) =
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N),P) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorSystemComparison l E f).hom.app (M,N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l E X).systemClosed.monoidal.associator
        ((pullbackTensorSequenceDerived l E f).obj M)
        ((pullbackTensorSequenceDerived l E f).obj N)
        ((pullbackTensorSequenceDerived l E f).obj P)).hom := by
  let P := A
  let Q := B
  let N := C
  have hP := hA
  have hQ := hB
  have hN := hC
  let J := coefficientSequenceTopology (ProEt.topology Y)
  let R := coefficientSequenceCommRingSheaf l E Y
  let J' := coefficientSequenceTopology (ProEt.topology X)
  let R' := coefficientSequenceCommRingSheaf l E X
  let U := pullbackTensorSequenceInverse l E f
  let SB := (pullbackTensorCalculus l E Y).systemClosed
  let TB := (pullbackTensorCalculus l E Y).systemTensorModel
  let SA := (pullbackTensorCalculus l E X).systemClosed
  let TA := (pullbackTensorCalculus l E X).systemTensorModel
  let μ := pullbackTensorSystemComparison l E f
  let chain := pullbackTensorSequenceCochain l E f
  have hCB := pullbackTensor_systemTensorCoherence l E Y
  have hCA := pullbackTensor_systemTensorCoherence l E X
  obtain ⟨βB, ⟨cB⟩⟩ := hCB
  obtain ⟨βA, ⟨cA⟩⟩ := hCA
  let := SB.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l E Y) :=
    SB.monoidal.toMonoidalCategoryStruct
  let := SA.monoidal
  let : MonoidalCategoryStruct (coefficientSequenceDerived l E X) :=
    SA.monoidal.toMonoidalCategoryStruct
  change U.mapDerivedCategory.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj N)).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (𝟙 (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ⊗ₘ
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
    μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⊗ₘ
        𝟙 (U.mapDerivedCategory.obj (DerivedCategory.Q.obj N))) ≫
      (α_ (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
        (U.mapDerivedCategory.obj (DerivedCategory.Q.obj Q))
        (U.mapDerivedCategory.obj (DerivedCategory.Q.obj N))).hom
  erw [id_tensorHom, tensorHom_id]
  let V := U.mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor.{u, u + 1, u} J R
  let A := coefficientTotalTensor.{u, u + 1, u} J' R'
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := coefficientTotalTensor_isKFlat.{u, u + 1, u} J R P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{u, u + 1, u} J R Q N hQ hN
  have hUP := pullbackTensorSequenceGood l E f P hP
  have hUQ := pullbackTensorSequenceGood l E f Q hQ
  have hUN := pullbackTensorSequenceGood l E f N hN
  have hUPQ := pullbackTensorSequenceGood l E f PQ hPQ
  have hUQN := pullbackTensorSequenceGood l E f QN hQN
  have hAPQ := coefficientTotalTensor_isKFlat.{u, u + 1, u} J' R' (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{u, u + 1, u} J' R' (V.obj Q) (V.obj N) hUQ hUN
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP hQ hN
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc := completedPullbackTensor_cochain_associativity l E f P Q N aB aA haB haA
  rw [show cB.tensorIso PQ N (Or.inr hN) = TB.iso J R SB PQ N hPQ hN from
      cB.tensorIso_both PQ N hPQ hN,
    cB.tensorIso_both P QN hP hQN] at heB
  rw [show cA.tensorIso (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inr hUN) =
      TA.iso J' R' SA _ _ hAPQ hUN from cA.tensorIso_both _ _ hAPQ hUN,
    cA.tensorIso_both (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN] at heA
  let bPQ := TB.iso J R SB P Q hP hQ
  let bQN := TB.iso J R SB Q N hQ hN
  let bL := TB.iso J R SB PQ N hPQ hN
  let bR := TB.iso J R SB P QN hP hQN
  let aPQ := TA.iso J' R' SA (V.obj P) (V.obj Q) hUP hUQ
  let aQN := TA.iso J' R' SA (V.obj Q) (V.obj N) hUQ hUN
  let aL := TA.iso J' R' SA (A.obj (V.obj P, V.obj Q)) (V.obj N) hAPQ hUN
  let aR := TA.iso J' R' SA (V.obj P) (A.obj (V.obj Q, V.obj N)) hUP hAQN
  let aL₀ := TA.iso J' R' SA (V.obj PQ) (V.obj N) hUPQ hUN
  let aR₀ := TA.iso J' R' SA (V.obj P) (V.obj QN) hUP hUQN
  let lB := bL ≪≫ whiskerRightIso bPQ (DerivedCategory.Q.obj N)
  let rB := bR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj P) bQN
  let lA := aL ≪≫ whiskerRightIso aPQ (DerivedCategory.Q.obj (V.obj N))
  let rA := aR ≪≫ whiskerLeftIso (DerivedCategory.Q.obj (V.obj P)) aQN
  let e : DerivedCategory.Q ⋙ U.mapDerivedCategory ≅ V ⋙ DerivedCategory.Q :=
    U.mapDerivedCategoryFactors
  let tPQ : DerivedCategory.Q.obj (V.obj PQ) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj P, V.obj Q)) :=
    DerivedCategory.Q.map (chain.hom.app (P, Q))
  let tQN : DerivedCategory.Q.obj (V.obj QN) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj Q, V.obj N)) :=
    DerivedCategory.Q.map (chain.hom.app (Q, N))
  let tL : DerivedCategory.Q.obj (V.obj (B.obj (PQ, N))) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj PQ, V.obj N)) :=
    DerivedCategory.Q.map (chain.hom.app (PQ, N))
  let tR : DerivedCategory.Q.obj (V.obj (B.obj (P, QN))) ⟶
      DerivedCategory.Q.obj (A.obj (V.obj P, V.obj QN)) :=
    DerivedCategory.Q.map (chain.hom.app (P, QN))
  let eL := e.hom.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      (chain.hom.app (P, Q), 𝟙 (V.obj N)))
  let eR := e.hom.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), chain.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    change (bL.hom ≫ (bPQ.hom ▷ DerivedCategory.Q.obj N)) ≫
        (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj N)).hom =
      DerivedCategory.Q.map aB.hom ≫ (bR.hom ≫ (DerivedCategory.Q.obj P ◁ bQN.hom))
    simpa only [bL, bR, bPQ, bQN, CoefficientClosedStructure.tensor, tensor_map,
      tensorHom_id, id_tensorHom, Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (V.obj P))
        (DerivedCategory.Q.obj (V.obj Q)) (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    change (aL.hom ≫ (aPQ.hom ▷ DerivedCategory.Q.obj (V.obj N))) ≫
        (α_ (DerivedCategory.Q.obj (V.obj P)) (DerivedCategory.Q.obj (V.obj Q))
          (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ (aR.hom ≫ (DerivedCategory.Q.obj (V.obj P) ◁ aQN.hom))
    simpa only [aL, aR, aPQ, aQN, CoefficientClosedStructure.tensor, tensor_map,
      tensorHom_id, id_tensorHom, Category.assoc] using heA
  have hμ := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec
  have hmPQ := hμ P Q hP hQ
  have hmQN := hμ Q N hQ hN
  have hmL := hμ PQ N hPQ hN
  have hmR := hμ P QN hP hQN
  change U.mapDerivedCategory.map bPQ.hom ≫ μ.hom.app (_, _) ≫
    ((e.hom.app P) ⊗ₘ (e.hom.app Q)) = e.hom.app _ ≫ tPQ ≫ aPQ.hom at hmPQ
  change U.mapDerivedCategory.map bQN.hom ≫ μ.hom.app (_, _) ≫
    ((e.hom.app Q) ⊗ₘ (e.hom.app N)) = e.hom.app _ ≫ tQN ≫ aQN.hom at hmQN
  change U.mapDerivedCategory.map bL.hom ≫ μ.hom.app (_, _) ≫
    ((e.hom.app PQ) ⊗ₘ (e.hom.app N)) = e.hom.app _ ≫ tL ≫ aL₀.hom at hmL
  change U.mapDerivedCategory.map bR.hom ≫ μ.hom.app (_, _) ≫
    ((e.hom.app P) ⊗ₘ (e.hom.app QN)) = e.hom.app _ ≫ tR ≫ aR₀.hom at hmR
  have hnL := TA.comparison.hom.naturality
    (X := (⟨V.obj PQ, hUPQ⟩, ⟨V.obj N, hUN⟩))
    (Y := (⟨A.obj (V.obj P, V.obj Q), hAPQ⟩, ⟨V.obj N, hUN⟩))
    (ObjectProperty.homMk (chain.hom.app (P, Q)), ObjectProperty.homMk (𝟙 (V.obj N)))
  change DerivedCategory.Q.map (A.map (chain.hom.app (P, Q), 𝟙 (V.obj N))) ≫ aL.hom =
    aL₀.hom ≫ SA.tensor.map
      (X := (DerivedCategory.Q.obj (V.obj PQ), DerivedCategory.Q.obj (V.obj N)))
      (Y := (DerivedCategory.Q.obj (A.obj (V.obj P, V.obj Q)),
        DerivedCategory.Q.obj (V.obj N)))
      (DerivedCategory.Q.map (chain.hom.app (P, Q)), DerivedCategory.Q.map (𝟙 (V.obj N))) at hnL
  have hnR := TA.comparison.hom.naturality
    (X := (⟨V.obj P, hUP⟩, ⟨V.obj QN, hUQN⟩))
    (Y := (⟨V.obj P, hUP⟩, ⟨A.obj (V.obj Q, V.obj N), hAQN⟩))
    (ObjectProperty.homMk (𝟙 (V.obj P)), ObjectProperty.homMk (chain.hom.app (Q, N)))
  change DerivedCategory.Q.map (A.map (𝟙 (V.obj P), chain.hom.app (Q, N))) ≫ aR.hom =
    aR₀.hom ≫ SA.tensor.map
      (X := (DerivedCategory.Q.obj (V.obj P), DerivedCategory.Q.obj (V.obj QN)))
      (Y := (DerivedCategory.Q.obj (V.obj P),
        DerivedCategory.Q.obj (A.obj (V.obj Q, V.obj N))))
      (DerivedCategory.Q.map (𝟙 (V.obj P)), DerivedCategory.Q.map (chain.hom.app (Q, N))) at hnR
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnL
  erw [tensorHom_id] at hnL
  simp only [CoefficientClosedStructure.tensor, tensor_map,
    DerivedCategory.Q.map_id] at hnR
  erw [id_tensorHom] at hnR
  have hL₀ := left_square
    U.mapDerivedCategory μ bPQ.hom bL.hom
    (e.hom.app P) (e.hom.app Q) (e.hom.app N) (e.hom.app PQ)
    (e.hom.app (B.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := right_square
    U.mapDerivedCategory μ bQN.hom bR.hom
    (e.hom.app P) (e.hom.app Q) (e.hom.app N) (e.hom.app QN)
    (e.hom.app (B.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : U.mapDerivedCategory.map lB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q,
        DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        U.mapDerivedCategory.obj (DerivedCategory.Q.obj N)) ≫
      (((e.hom.app P) ⊗ₘ (e.hom.app Q)) ⊗ₘ (e.hom.app N)) = eL ≫ lA.hom := by
    calc
      _ = e.hom.app (B.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ DerivedCategory.Q.obj (V.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
  have hR : U.mapDerivedCategory.map rB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P,
        DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      ((e.hom.app P) ⊗ₘ ((e.hom.app Q) ⊗ₘ (e.hom.app N))) = eR ≫ rA.hom := by
    calc
      _ = e.hom.app (B.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (DerivedCategory.Q.obj (V.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
  have hC := localization_comparison_paste DerivedCategory.Q DerivedCategory.Q
    U.mapDerivedCategory V e _ _ _ _ _ _ hc
  refine associativity_transport
    U.mapDerivedCategory μ lB rB (DerivedCategory.Q.map aB.hom)
    lA.hom rA.hom (DerivedCategory.Q.map aA.hom) (e.app P) (e.app Q) (e.app N)
    eL eR ?_ ?_ ?_ ?_ ?_
  · exact hB
  · exact hA
  · exact hL
  · exact hR
  · exact hC

end WeilConjectures
