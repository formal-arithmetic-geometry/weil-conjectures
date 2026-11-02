/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorAssociativityModelData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-! # Associativity on simultaneous resolving representatives

Source: Stacks 07A4 and 0FPT.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r wb d vd s wa b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace WeilConjectures

attribute [local implicit_reducible] CoefficientClosedStructure.tensor
  CategoryTheory.uniformProd
  CategoryTheory.MonoidalCategory.leftAssocTensor
  CategoryTheory.MonoidalCategory.rightAssocTensor

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]

variable (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory _ _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory _ _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (K : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
    CochainComplex (RingedTensorModules.{d, vd, s} J' R') ℤ)
  (F : DerivedCategory (RingedTensorModules.{c, v, r} J R) ⥤
    DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
  (ε : DerivedCategory.Q ⋙ F ⟶ K ⋙ DerivedCategory.Q)
  (hε : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) → IsIso (ε.app P))
  (hU : ∀ (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ),
    P.IsKFlatIndependentCoefficients →
    (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) →
    CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
  (chain : coefficientTotalTensor.{r, c, v} J R ⋙ K ≅
    K.prod K ⋙ coefficientTotalTensor.{s, d, vd} J' R')
  (hκ : CoefficientComplexTensorAssociativity J R J' R' K chain)
  (μ : SB.tensor ⋙ F ≅ F.prod F ⋙ SA.tensor)
  (hμ : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients)
    (hUP : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj P))
    (hUQ : CochainComplex.IsKFlatIndependentCoefficients (R := R') (K.obj Q))
    (_fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (_fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p)),
    F.map (TB.iso J R SB P Q hP hQ).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        SA.tensor.map
          (X := (F.obj (DerivedCategory.Q.obj P), F.obj (DerivedCategory.Q.obj Q)))
          (Y := (DerivedCategory.Q.obj (K.obj P), DerivedCategory.Q.obj (K.obj Q)))
          (Prod.mkHom (ε.app P) (ε.app Q)) =
      ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
        DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
        (TA.iso J' R' SA (K.obj P) (K.obj Q) hUP hUQ).hom)

omit [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)] in
private theorem coefficient_total_eq :
    coefficientTotalTensor.{r, c, v} J R = SheafOfModules.KFlatTotalTensorModel.total R := by
  rfl

include cB cA hε hU hκ hμ

attribute [local irreducible] coefficientTotalTensor SheafOfModules.monoidalCategory

set_option maxHeartbeats 800000 in
-- Paste the four model squares without unfolding localization constructions.
/-- Paste four binary representative squares and the ordinary associativity equation.
Source: Stacks 07A4 and 0FPT.
(blueprint: lem-coef-tensor-associativity-representatives). -/
theorem coefficientTensorAssociativityOnRepresentatives
    (P Q N : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p))
    (hQ : Q.IsKFlatIndependentCoefficients)
    (fQ : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (Q.X p))
    (hN : N.IsKFlatIndependentCoefficients)
    (fN : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (N.X p)) :
    F.map (SB.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom ≫
        μ.hom.app (DerivedCategory.Q.obj P,
          SB.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
        SA.tensor.map (Prod.mkHom (𝟙 (F.obj (DerivedCategory.Q.obj P)))
          (μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N))) =
      μ.hom.app (SB.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
        DerivedCategory.Q.obj N) ≫
        SA.tensor.map (Prod.mkHom
          (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q))
          (𝟙 (F.obj (DerivedCategory.Q.obj N)))) ≫
        (SA.monoidal.associator (F.obj (DerivedCategory.Q.obj P))
          (F.obj (DerivedCategory.Q.obj Q)) (F.obj (DerivedCategory.Q.obj N))).hom := by
  let := SB.monoidal
  let := SA.monoidal
  change F.map (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
      (DerivedCategory.Q.obj N)).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q ⊗ DerivedCategory.Q.obj N) ≫
      (𝟙 (F.obj (DerivedCategory.Q.obj P)) ⊗ₘ
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) =
    μ.hom.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⊗ₘ
        𝟙 (F.obj (DerivedCategory.Q.obj N))) ≫
      (α_ (F.obj (DerivedCategory.Q.obj P))
        (F.obj (DerivedCategory.Q.obj Q))
        (F.obj (DerivedCategory.Q.obj N))).hom
  erw [id_tensorHom, tensorHom_id]
  let V := K
  let := hε P hP fP
  let := hε Q hQ fQ
  let := hε N hN fN
  let B := coefficientTotalTensor.{r, c, v} J R
  let A := coefficientTotalTensor.{s, d, vd} J' R'
  let PQ := B.obj (P, Q)
  let QN := B.obj (Q, N)
  have hPQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ
  have hQN := coefficientTotalTensor_isKFlat.{r, c, v} J R Q N hQ hN
  have fPQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (PQ.X i) := by
    dsimp only [PQ, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R P Q hP hQ fP fQ).2.1
  have fQN : ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (J := J) (R := R) (QN.X i) := by
    dsimp only [QN, B]
    rw [coefficient_total_eq]
    exact (SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
      R Q N hQ hN fQ fN).2.1
  have hUP := hU P hP fP
  have hUQ := hU Q hQ fQ
  have hUN := hU N hN fN
  have hUPQ := hU PQ hPQ fPQ
  have hUQN := hU QN hQN fQN
  have hAPQ := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj P) (V.obj Q) hUP hUQ
  have hAQN := coefficientTotalTensor_isKFlat.{s, d, vd} J' R' (V.obj Q) (V.obj N) hUQ hUN
  obtain ⟨aB, haB, heB⟩ := cB.associator_model P Q N hP hQ hN
  obtain ⟨aA, haA, heA⟩ := cA.associator_model (V.obj P) (V.obj Q) (V.obj N) hUP hUQ hUN
  have hc : V.map aB.hom ≫ chain.hom.app (P, QN) ≫
        A.map (X := (V.obj P, V.obj QN))
          (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), chain.hom.app (Q, N)) =
      chain.hom.app (PQ, N) ≫
        A.map (X := (V.obj PQ, V.obj N))
          (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
          (chain.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom := by
    exact hκ P Q N aB aA haB haA
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
  let e := ε
  let tPQ := DerivedCategory.Q.map (chain.hom.app (P, Q))
  let tQN := DerivedCategory.Q.map (chain.hom.app (Q, N))
  let tL := DerivedCategory.Q.map (chain.hom.app (PQ, N))
  let tR := DerivedCategory.Q.map (chain.hom.app (P, QN))
  let eL := e.app (B.obj (PQ, N)) ≫ tL ≫
    DerivedCategory.Q.map (A.map (X := (V.obj PQ, V.obj N))
      (Y := (A.obj (V.obj P, V.obj Q), V.obj N))
      (chain.hom.app (P, Q), 𝟙 (V.obj N)))
  let eR := e.app (B.obj (P, QN)) ≫ tR ≫
    DerivedCategory.Q.map (A.map (X := (V.obj P, V.obj QN))
      (Y := (V.obj P, A.obj (V.obj Q, V.obj N)))
      (𝟙 (V.obj P), chain.hom.app (Q, N)))
  have hB : lB.hom ≫ (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj N)).hom = DerivedCategory.Q.map aB.hom ≫ rB.hom := by
    simpa only [lB, rB, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_obj, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heB
  have hA : lA.hom ≫ (α_ (DerivedCategory.Q.obj (V.obj P))
        (DerivedCategory.Q.obj (V.obj Q)) (DerivedCategory.Q.obj (V.obj N))).hom =
      DerivedCategory.Q.map aA.hom ≫ rA.hom := by
    simpa only [lA, rA, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom,
      CoefficientClosedStructure.tensor, tensor_obj, tensor_map, tensorHom_id, id_tensorHom,
      Category.assoc] using heA
  have hmPQ := hμ P Q hP hQ hUP hUQ fP fQ
  have hmQN := hμ Q N hQ hN hUQ hUN fQ fN
  have hmL := hμ PQ N hPQ hN hUPQ hUN fPQ fN
  have hmR := hμ P QN hP hQN hUP hUQN fP fQN
  have hnL := cA.tensorIso_naturality (V.obj PQ) (V.obj N)
    (A.obj (V.obj P, V.obj Q)) (V.obj N) (Or.inl hUPQ) (Or.inl hAPQ)
    (chain.hom.app (P, Q)) (𝟙 (V.obj N))
  rw [cA.tensorIso_both _ _ hUPQ hUN, cA.tensorIso_both _ _ hAPQ hUN] at hnL
  have hnR := cA.tensorIso_naturality (V.obj P) (V.obj QN)
    (V.obj P) (A.obj (V.obj Q, V.obj N)) (Or.inl hUP) (Or.inl hUP)
    (𝟙 (V.obj P)) (chain.hom.app (Q, N))
  rw [cA.tensorIso_both _ _ hUP hUQN, cA.tensorIso_both _ _ hUP hAQN] at hnR
  simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
    DerivedCategory.Q.map_id] at hnL
  erw [tensorHom_id] at hnL
  simp only [CoefficientClosedStructure.tensor, tensor_obj, tensor_map,
    DerivedCategory.Q.map_id] at hnR
  erw [id_tensorHom] at hnR
  have hL₀ := left_square F μ bPQ.hom bL.hom
    (e.app P) (e.app Q) (e.app N) (e.app PQ)
    (e.app (B.obj (PQ, N))) (tPQ ≫ aPQ.hom) (tL ≫ aL₀.hom) hmPQ hmL
  have hR₀ := right_square F μ bQN.hom bR.hom
    (e.app P) (e.app Q) (e.app N) (e.app QN)
    (e.app (B.obj (P, QN))) (tQN ≫ aQN.hom) (tR ≫ aR₀.hom) hmQN hmR
  have hL : F.map lB.hom ≫
      μ.hom.app (SB.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q),
        DerivedCategory.Q.obj N) ≫
      (μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ▷
        F.obj (DerivedCategory.Q.obj N)) ≫
      (((e.app P) ⊗ₘ (e.app Q)) ⊗ₘ (e.app N)) = eL ≫ lA.hom := by
    calc
      _ = e.app (B.obj (PQ, N)) ≫ (tL ≫ aL₀.hom) ≫
          ((tPQ ≫ aPQ.hom) ▷ DerivedCategory.Q.obj (V.obj N)) := hL₀
      _ = _ := by
        simp only [comp_whiskerRight, Category.assoc]
        erw [← reassoc_of% hnL]
        simp only [eL, lA, Iso.trans_hom, whiskerRightIso_hom, Category.assoc]
        rfl
  have hR : F.map rB.hom ≫
      μ.hom.app (DerivedCategory.Q.obj P,
        SB.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      (F.obj (DerivedCategory.Q.obj P) ◁
        μ.hom.app (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj N)) ≫
      ((e.app P) ⊗ₘ ((e.app Q) ⊗ₘ (e.app N))) = eR ≫ rA.hom := by
    calc
      _ = e.app (B.obj (P, QN)) ≫ (tR ≫ aR₀.hom) ≫
          (DerivedCategory.Q.obj (V.obj P) ◁ (tQN ≫ aQN.hom)) := hR₀
      _ = _ := by
        simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
        erw [← reassoc_of% hnR]
        simp only [eR, rA, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
        rfl
  have hC : F.map (DerivedCategory.Q.map aB.hom) ≫ eR =
      eL ≫ DerivedCategory.Q.map aA.hom := by
    have hf := e.naturality aB.hom
    change F.map (DerivedCategory.Q.map aB.hom) ≫
        e.app (B.obj (P, QN)) = e.app (B.obj (PQ, N)) ≫
          DerivedCategory.Q.map (V.map aB.hom) at hf
    dsimp only [eL, eR]
    rw [reassoc_of% hf]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f ↦ e.app (B.obj (PQ, N)) ≫ DerivedCategory.Q.map f) hc
  exact associativity_transport F μ lB rB (DerivedCategory.Q.map aB.hom)
    lA.hom rA.hom (DerivedCategory.Q.map aA.hom) (asIso (e.app P))
    (asIso (e.app Q)) (asIso (e.app N))
    eL eR hB hA hL hR hC

end WeilConjectures
