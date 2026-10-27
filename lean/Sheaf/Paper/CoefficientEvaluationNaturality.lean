/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.SixFunctorDatum
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.Paper.CoefficientTwistInterchange
public import Sheaf.Paper.DlLocallyConstructibleAdicHeart
import Sheaf.Paper.ShiftedCoefficientLinesInvertible

/-! # Naturality of coefficient evaluation

Source: main-20261015, sk-thm-sf-dual-perfect, proof sentences 1--3,
and sk-lem-sf-twist-interchange, proof paragraph 1
(blueprint: lem-sf-coefficient-evaluation-naturality).
The comparison below is the existing evaluation-defined comparison. All four
coefficient stages use their recorded closed presentations, including signed symmetry.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u a b
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Theta is internal Hom of gamma inverse followed by the inverse of the canonical
coefficient comparison. Source: dual-perfect proof sentences 1--3
(blueprint: lem-sf-coefficient-evaluation-naturality). -/
def sfCoefficientTheta {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)
    {L W : B} (gamma : L ≅ W) (P : B)
    (hc : IsIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit
      (Iso.refl _) P L)) :
    H.obj (op P, W) ≅ S.tensor.obj (H.obj (op P, S.monoidal.tensorUnit), L) :=
  haveI := hc
  H.mapIso (Iso.prod (Iso.refl (op P)) gamma.symm) ≪≫
    (asIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P L)).symm

/-- All evaluation and naturality equations, including an arbitrary full subcategory
of invertible comparison maps. Source: dual-perfect proof sentences 1--3
(blueprint: lem-sf-coefficient-evaluation-naturality). -/
def SfCoefficientEvaluationLaws {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal) : Prop :=
  (∀ P M : B,
    ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P M =
      S.transpose _ P M
        ((S.monoidal.associator _ M P).hom ≫
          S.tensor.map (Prod.mkHom (𝟙 _) (s.braiding M P).hom) ≫
          (S.monoidal.associator _ P M).inv ≫
          S.tensor.map (Prod.mkHom (S.evaluation P S.monoidal.tensorUnit) (𝟙 M)) ≫
          (S.monoidal.leftUnitor M).hom)) ∧
  (∀ (P P' M M' : B) (u : P ⟶ P') (v : M ⟶ M'),
    ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P' M ≫
        H.map (Prod.mkHom u.op v) =
      S.tensor.map
        (Prod.mkHom (H.map (Prod.mkHom u.op (𝟙 S.monoidal.tensorUnit))) v) ≫
        ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P M') ∧
  (∀ (J : ObjectProperty B) (L W : B) (gamma : L ≅ W)
      (hc : ∀ P : J.FullSubcategory,
        IsIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P.obj L)),
    (∀ (P P' : J.FullSubcategory) (u : P ⟶ P'),
      H.map (Prod.mkHom u.hom.op (𝟙 W)) ≫
          (sfCoefficientTheta S s gamma P.obj (hc P)).hom =
        (sfCoefficientTheta S s gamma P'.obj (hc P')).hom ≫
          S.tensor.map
            (Prod.mkHom (H.map (Prod.mkHom u.hom.op (𝟙 S.monoidal.tensorUnit))) (𝟙 L))) ∧
    (∀ P : J.FullSubcategory,
      S.tensor.map (Prod.mkHom (sfCoefficientTheta S s gamma P.obj (hc P)).inv
          (𝟙 P.obj)) ≫ S.evaluation P.obj W =
        (S.monoidal.associator _ L P.obj).hom ≫
          S.tensor.map (Prod.mkHom (𝟙 _) (s.braiding L P.obj).hom) ≫
          (S.monoidal.associator _ P.obj L).inv ≫
          S.tensor.map (Prod.mkHom (S.evaluation P.obj S.monoidal.tensorUnit) (𝟙 L)) ≫
          (S.monoidal.leftUnitor L).hom ≫ gamma.hom))

/-- The perfect shifted-line clause, with the canonical interchange isomorphism,
read on the actual full subcategory. Membership of the line is asserted.
Source: twist-interchange proof final paragraph
(blueprint: lem-sf-coefficient-evaluation-naturality). -/
def SfCoefficientTwistEvaluation
    {B : Type a} [Category.{b} B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H) (L : B) : Prop :=
  ∃ hL : P L,
    ∃ hT : @IsInvertible _ _ M.closed.monoidal (⟨L, hL⟩ : P.FullSubcategory),
      ∀ (K : P.FullSubcategory) (hK : @IsDualizable _ _ M.closed.monoidal K),
        ∃ _hc : IsIso (ringedSiteDualEvaluationLeft M.closed M.symmetric
          M.closed.monoidal.tensorUnit (Iso.refl _) K ⟨L, hL⟩),
          (asIso (ringedSiteDualEvaluationLeft M.closed M.symmetric
            M.closed.monoidal.tensorUnit (Iso.refl _) K ⟨L, hL⟩)).symm =
            sfCoefficientTwistIso M.closed M.symmetric K ⟨L, hL⟩ hK hT

/-- The recorded signed completed Tate line, with an arbitrary integral shift.
Residue invertibility is supplied by the finite-field coefficient datum.
Source: coefficient-twists-detailed and dual-perfect proof sentences 1--3
(blueprint: lem-sf-coefficient-evaluation-naturality). -/
def sfEvaluationIntegralLine (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D) (m t : ℤ) :
    sfIntegralConstructibleCategory C.l E X.obj.left :=
  (@sfIntegralTwistingCoefficient C.l _ E _ _ _ X.obj.left
    (dlAdicGeometricResidueInvertible D C X.obj.left) m)⟦t⟧

section Evaluation
variable {B : Type a} [Category.{b} B] {H : Bᵒᵖ × B ⥤ B}
  (S : CoefficientClosedStructure H) (s : @SymmetricCategory B _ S.monoidal)

open MonoidalCategory

private theorem evaluation_formula (P M : B) :
    ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P M =
      S.transpose _ P M
        ((S.monoidal.associator _ M P).hom ≫
          S.tensor.map (Prod.mkHom (𝟙 _) (s.braiding M P).hom) ≫
          (S.monoidal.associator _ P M).inv ≫
          S.tensor.map (Prod.mkHom (S.evaluation P S.monoidal.tensorUnit) (𝟙 M)) ≫
          (S.monoidal.leftUnitor M).hom) := by
  let _ := S.monoidal
  let _ := s
  unfold ringedSiteDualEvaluationLeft ringedSiteDualEvaluation
    CoefficientClosedStructure.transpose
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  erw [← (S.adjunction P).homEquiv_naturality_left]
  congr 1
  dsimp only [CoefficientClosedStructure.tensor, Iso.refl_inv]
  dsimp only [tensorRight, Functor.flip, curriedTensor]
  simp only [tensorHom_id, id_tensorHom, id_whiskerRight, Category.id_comp]
  rw [← braiding_leftUnitor M]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rw [BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, Category.id_comp]

private theorem evaluation_source {P P' : B} (f : P ⟶ P') (M : B) :
    ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P' M ≫
        H.map (Prod.mkHom f.op (𝟙 M)) =
      S.tensor.map (Prod.mkHom
        (H.map (Prod.mkHom f.op (𝟙 S.monoidal.tensorUnit))) (𝟙 M)) ≫
        ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P M := by
  let _ := S.monoidal
  let _ := s
  unfold ringedSiteDualEvaluationLeft
  rw [Category.assoc, ← ringedSiteDualEvaluation_source_naturality]
  dsimp only [CoefficientClosedStructure.tensor]
  simp only [tensor_map, tensorHom_id, id_tensorHom]
  rw [BraidedCategory.braiding_naturality_left_assoc]

private theorem evaluation_natural (P P' M M' : B) (u : P ⟶ P') (v : M ⟶ M') :
    ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P' M ≫
        H.map (Prod.mkHom u.op v) =
      S.tensor.map
        (Prod.mkHom (H.map (Prod.mkHom u.op (𝟙 S.monoidal.tensorUnit))) v) ≫
        ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P M' := by
  have hh : H.map (Prod.mkHom u.op v) =
      H.map (Prod.mkHom u.op (𝟙 M)) ≫ H.map (Prod.mkHom (𝟙 (op P)) v) := by
    rw [← H.map_comp]
    congr 1
    ext <;> simp
  rw [hh, ← Category.assoc, evaluation_source, Category.assoc,
    ← ringedSiteDualEvaluationLeft_naturality, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp

private theorem evaluation_laws : SfCoefficientEvaluationLaws S s := by
  refine ⟨evaluation_formula S s, evaluation_natural S s, ?_⟩
  intro J L W gamma hc
  have hc' (P : J.FullSubcategory) := hc P
  refine ⟨?_, ?_⟩
  · intro P P' u
    apply (cancel_mono
      (asIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit
        (Iso.refl _) P.obj L)).hom).1
    simp only [sfCoefficientTheta, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.prod_hom, Iso.refl_hom, asIso_hom, asIso_inv, Category.assoc]
    rw [IsIso.inv_hom_id, Category.comp_id]
    rw [← evaluation_source S s u.hom L, IsIso.inv_hom_id_assoc]
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    ext <;> simp
  · intro P
    let _ := S.monoidal
    simp only [sfCoefficientTheta, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Iso.prod_inv, Iso.refl_inv, asIso_hom]
    have hev := (S.adjunction P.obj).counit.naturality gamma.hom
    simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id]
    change (tensorRight P.obj).map
      (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P.obj L ≫
        H.map (Prod.mkHom (𝟙 (op P.obj)) gamma.hom)) ≫ S.evaluation P.obj W = _
    rw [Functor.map_comp, Category.assoc]
    rw [show (tensorRight P.obj).map
        (H.map (Prod.mkHom (𝟙 (op P.obj)) gamma.hom)) ≫ S.evaluation P.obj W =
        S.evaluation P.obj L ≫ gamma.hom from hev]
    rw [← Category.assoc]
    change (S.transpose _ P.obj L).symm
      (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P.obj L) ≫
      gamma.hom = _
    rw [evaluation_formula]
    erw [Equiv.symm_apply_apply]
    simp only [CoefficientClosedStructure.tensor, tensor_map, tensorHom_id,
      Category.assoc]

private theorem twist_comparison (P L : B)
    (hP : @IsDualizable B _ S.monoidal P) (hL : @IsInvertible B _ S.monoidal L) :
    ∃ _hc : IsIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit
        (Iso.refl _) P L),
      (asIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit
        (Iso.refl _) P L)).symm = sfCoefficientTwistIso S s P L hP hL := by
  have he : ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit (Iso.refl _) P L =
      sfTwistTensorHomMap S s P S.monoidal.tensorUnit L ≫
        H.map (Prod.mkHom (𝟙 (op P)) (S.monoidal.leftUnitor L).hom) := by
    rw [evaluation_formula]
    unfold sfTwistTensorHomMap CoefficientClosedStructure.transpose
    dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
    erw [← (S.adjunction P).homEquiv_naturality_right]
    congr 1
    simp only [Category.assoc]
  have _ := sfTwistTensorHomMap_isIso S s P S.monoidal.tensorUnit L hP hL
  have _ : IsIso (H.map
      (Prod.mkHom (𝟙 (op P)) (S.monoidal.leftUnitor L).hom)) :=
    (H.mapIso (Iso.prod (Iso.refl (op P)) (S.monoidal.leftUnitor L))).isIso_hom
  have hc : IsIso (ringedSiteDualEvaluationLeft S s S.monoidal.tensorUnit
      (Iso.refl _) P L) := by rw [he]; infer_instance
  refine ⟨hc, ?_⟩
  apply Iso.symm_bijective.injective
  apply Iso.ext
  simpa only [sfCoefficientTwistIso, sfTwistTensorHomIso, Iso.trans_inv,
    Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv, Iso.prod_inv, Iso.refl_inv,
    asIso_hom] using he

private theorem twist_evaluation
    {P : ObjectProperty B} {Q : ObjectProperty (Bᵒᵖ × B)}
    {H' : Q.FullSubcategory ⥤ B} (M : SixFunctorClosedDomain P Q H')
    (L : B) (hL : P L)
    (hT : @IsInvertible _ _ M.closed.monoidal (⟨L, hL⟩ : P.FullSubcategory)) :
    SfCoefficientTwistEvaluation M L := by
  refine ⟨hL, hT, ?_⟩
  intro K hK
  exact twist_comparison M.closed M.symmetric K ⟨L, hL⟩ hK hT

end Evaluation

/-- Coefficient evaluation is natural at all four actual coefficient stages.
The last four clauses include every integer twist and shift, with the inverse
comparison equal to canonical twist interchange. No exceptional map or orientation
is assumed. Source: dual-perfect proof sentences 1--3 and twist-interchange proof
(blueprint: lem-sf-coefficient-evaluation-naturality).

Proof: (1) The tensor-Hom adjunction in sk-def-sf-operations gives the inverse
transpose as evaluation after tensoring the arrow with identity. Its naturality
in the source gives evaluation dinaturality. The uncurry laws of
lem-pod-closed-uncurry-laws identify the transpose of c with the displayed
coefficient evaluation and signed interchange. (2) Transpose the two sides of
the two-variable naturality equation. Naturality of symmetry and the preceding
evaluation dinaturality identify their composites, and injectivity of transpose
identifies the arrows. (3) On the arbitrary full subcategory J cancel its
invertible comparison maps to obtain contravariant theta naturality. Its inverse
is c followed by H(P,gamma); transposing this formula gives exactly the evaluation
equation. (4) For the shifted Tate line, coefficient-twists-detailed gives the
invertible signed line at every integer twist and shift. Apply
sk-lem-sf-twist-interchange with target the coefficient unit. Its evaluation
transpose followed by the unitor is c, so its inverse is exactly the canonical
isomorphism in the statement. Use the completed unit integrally, rationalize
at E, and pass to a common finite stage at Qbar. -/
theorem sfCoefficientEvaluationNaturality
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {n : ℕ}
    (S : SixFunctorDatum D C E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
    (X : SixFunctorSpace D) :
    SfCoefficientEvaluationLaws (S.finiteClosed X).closed (S.finiteClosed X).symmetric ∧
    SfCoefficientEvaluationLaws (S.integralClosed X).closed (S.integralClosed X).symmetric ∧
    SfCoefficientEvaluationLaws (S.rationalClosed X).closed (S.rationalClosed X).symmetric ∧
    SfCoefficientEvaluationLaws (S.commonClosed X).closed (S.commonClosed X).symmetric ∧
    (∀ m t : ℤ, SfCoefficientTwistEvaluation (S.finiteClosed X)
      ((sixFunctorIntegralReduction D C E n X).obj (sfEvaluationIntegralLine D C E X m t))) ∧
    (∀ m t : ℤ, SfCoefficientTwistEvaluation (S.integralClosed X)
      (sfEvaluationIntegralLine D C E X m t)) ∧
    (∀ m t : ℤ, SfCoefficientTwistEvaluation (S.rationalClosed X)
      ((@sfRationalTwistingCoefficient C.l _ E _ _ _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left) m)⟦t⟧)) ∧
    (∀ m t : ℤ, SfCoefficientTwistEvaluation (S.commonClosed X)
      ((@sfQbarTwistingCoefficient C.l _ X.obj.left
        (dlAdicGeometricResidueInvertible D C X.obj.left) C.Qbar _ _ _ m)⟦t⟧)) := by
  refine ⟨evaluation_laws _ _, evaluation_laws _ _, evaluation_laws _ _,
    evaluation_laws _ _, ?_, ?_, ?_, ?_⟩
  · intro m t
    obtain ⟨hL, hT⟩ := (sfShiftedCoefficientLinesInvertible S X m t).1
    exact twist_evaluation (S.finiteClosed X) _ hL hT
  · intro m t
    obtain ⟨hL, hT⟩ := (sfShiftedCoefficientLinesInvertible S X m t).2.1
    exact twist_evaluation (S.integralClosed X) _ hL hT
  · intro m t
    obtain ⟨hL, hT⟩ := (sfShiftedCoefficientLinesInvertible S X m t).2.2.1
    exact twist_evaluation (S.rationalClosed X) _ hL hT
  · intro m t
    obtain ⟨hL, hT⟩ := (sfShiftedCoefficientLinesInvertible S X m t).2.2.2
    exact twist_evaluation (S.commonClosed X) _ hL hT

end WeilConjectures
