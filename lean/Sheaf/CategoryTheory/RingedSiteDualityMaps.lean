/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
/-! # Canonical coefficient-duality maps on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A97 and 0A98
(blueprint: lem-sfb-ringed-site-duality-maps).
The existing closed tensor-Hom representative model pins transposition to actual
sheafified pure tensors. The unit, associator and symmetry below are pinned to
ordinary complexes as well. No perfectness or invertibility is part of this model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w w' a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open SheafOfModules
namespace CategoryTheory

section Closed
variable {D : Type a} [Category.{b} D] {H : Dᵒᵖ × D ⥤ D}
  (S : WeilConjectures.CoefficientClosedStructure H)
  (s : @SymmetricCategory D _ S.monoidal)
  (O : D) (u : S.monoidal.tensorUnit ≅ O)

/-- Transpose of coefficient evaluation after Koszul interchange.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteBidual (P : D) : P ⟶ H.obj (op (H.obj (op P, O)), O) :=
  S.transpose P (H.obj (op P, O)) O
    ((s.braiding P (H.obj (op P, O))).hom ≫ S.evaluation P O)

/-- Tensor with the coefficient dual, in the order of Tag 08JE.
Source: Stacks 08JE (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualTensor (P : D) : D ⥤ D :=
  Prod.sectL D (H.obj (op P, O)) ⋙ S.tensor

/-- The canonical comparison, defined by transposing composite evaluations.
Its source is N tensor the dual; symmetry gives the order in perfect duality.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluation (P N : D) :
    S.tensor.obj (N, H.obj (op P, O)) ⟶ H.obj (op P, N) :=
  S.transpose _ P N
    ((S.monoidal.associator N (H.obj (op P, O)) P).hom ≫
      S.tensor.map (Prod.mkHom (𝟙 N) (S.evaluation P O)) ≫
      S.tensor.map (Prod.mkHom (𝟙 N) u.inv) ≫ (S.monoidal.rightUnitor N).hom)

/-- Naturality of the actual evaluation comparison in the second variable.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose both sides. Naturality of the associator, tensor, right unitor,
and the adjunction counit makes the resulting composite evaluations equal. -/
theorem ringedSiteDualEvaluation_naturality (P : D) {N N' : D} (f : N ⟶ N') :
    S.tensor.map (Prod.mkHom f (𝟙 (H.obj (op P, O)))) ≫
        ringedSiteDualEvaluation S O u P N' =
      ringedSiteDualEvaluation S O u P N ≫ H.map (Prod.mkHom (𝟙 (op P)) f) := by
  let _ := S.monoidal
  unfold ringedSiteDualEvaluation WeilConjectures.CoefficientClosedStructure.transpose
  apply (S.adjunction P).homEquiv_naturality_left_square
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [Category.assoc]
  simp only [tensorHom_id, id_tensorHom,
    associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]

/-- Evaluation as a natural transformation, with the specified canonical components.
Source: Stacks 08JD (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluationNatTrans (P : D) :
    ringedSiteDualTensor S O P ⟶ Prod.sectR (op P) D ⋙ H where
  app N := ringedSiteDualEvaluation S O u P N
  naturality _ _ f := ringedSiteDualEvaluation_naturality S O u P f

private theorem ringedSiteTranspose_left {T T' P Q : D} (f : T' ⟶ T)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T' P Q (S.tensor.map (Prod.mkHom f (𝟙 P)) ≫ g) =
      f ≫ S.transpose T P Q g := by
  let _ := S.monoidal
  dsimp only [WeilConjectures.CoefficientClosedStructure.transpose,
    WeilConjectures.CoefficientClosedStructure.tensor, MonoidalCategory.tensor]
  rw [tensorHom_id]
  exact (S.adjunction P).homEquiv_naturality_left f g

private theorem ringedSiteTranspose_source (T : D) {P P' Q : D} (f : P' ⟶ P)
    (g : S.tensor.obj (T, P) ⟶ Q) :
    S.transpose T P' Q (S.tensor.map (Prod.mkHom (𝟙 T) f) ≫ g) =
      S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q)) := by
  let _ := S.monoidal
  apply (S.transpose T P' Q).symm.injective
  rw [Equiv.symm_apply_apply]
  change _ = (tensorRight P').map
    (S.transpose T P Q g ≫ H.map (Prod.mkHom f.op (𝟙 Q))) ≫ S.evaluation P' Q
  rw [Functor.map_comp, Category.assoc]
  change _ = (S.transpose T P Q g ▷ P') ≫
    (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q
  rw [show (H.map (Prod.mkHom f.op (𝟙 Q)) ▷ P') ≫ S.evaluation P' Q =
    (H.obj (op P, Q) ◁ f) ≫ S.evaluation P Q from S.evaluation_naturality P P' Q f]
  rw [← Category.assoc, ← whisker_exchange, Category.assoc]
  change _ = (T ◁ f) ≫ (S.transpose T P Q).symm (S.transpose T P Q g)
  rw [Equiv.symm_apply_apply]
  simp only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map,
    id_tensorHom]

/-- Naturality of signed bidual evaluation in the source complex.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose, apply naturality of braiding, and then evaluation_naturality.
Adjunction naturality turns this identity back into the displayed equation. -/
theorem ringedSiteBidual_naturality {P P' : D} (f : P ⟶ P') :
    f ≫ ringedSiteBidual S s O P' =
      ringedSiteBidual S s O P ≫ H.map
        (Prod.mkHom (H.map (Prod.mkHom f.op (𝟙 O))).op (𝟙 O)) := by
  let _ := S.monoidal
  let _ := s
  unfold ringedSiteBidual
  rw [← ringedSiteTranspose_left]
  rw [← ringedSiteTranspose_source]
  congr 1
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [id_tensorHom, tensorHom_id,
    BraidedCategory.braiding_naturality_left_assoc,
    BraidedCategory.braiding_naturality_right_assoc]
  congr 1
  exact (S.evaluation_naturality P' P O f).symm

/-- Evaluation is contravariantly natural in the first argument too.
Source: Stacks 08JD, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose and use evaluation_naturality, then associator naturality. -/
theorem ringedSiteDualEvaluation_source_naturality {P P' : D} (f : P' ⟶ P) (N : D) :
    S.tensor.map (Prod.mkHom (𝟙 N) (H.map (Prod.mkHom f.op (𝟙 O)))) ≫
        ringedSiteDualEvaluation S O u P' N =
      ringedSiteDualEvaluation S O u P N ≫ H.map (Prod.mkHom f.op (𝟙 N)) := by
  let _ := S.monoidal
  unfold ringedSiteDualEvaluation
  rw [← ringedSiteTranspose_left]
  rw [← ringedSiteTranspose_source]
  congr 1
  dsimp [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [id_tensorHom, tensorHom_id,
    associator_naturality_middle_assoc, associator_naturality_right_assoc]
  have ev : (H.map (Prod.mkHom f.op (𝟙 O)) ▷ P') ≫ S.evaluation P' O =
      (H.obj (op P, O) ◁ f) ≫ S.evaluation P O := S.evaluation_naturality P P' O f
  rw [← whiskerLeft_comp_assoc, ev]
  simp only [whiskerLeft_comp, Category.assoc]

/-- The canonical comparison with dual tensor the target, in the node's order.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluationLeft (P N : D) :
    S.tensor.obj (H.obj (op P, O), N) ⟶ H.obj (op P, N) :=
  (s.braiding (H.obj (op P, O)) N).hom ≫ ringedSiteDualEvaluation S O u P N

/-- Naturality after the Koszul symmetry that interchanges the two tensor factors.
Source: Stacks 08JE (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: use braiding naturality, then ringedSiteDualEvaluation_naturality. -/
theorem ringedSiteDualEvaluationLeft_naturality (P : D) {N N' : D} (f : N ⟶ N') :
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op P, O))) f) ≫
        ringedSiteDualEvaluationLeft S s O u P N' =
      ringedSiteDualEvaluationLeft S s O u P N ≫ H.map (Prod.mkHom (𝟙 (op P)) f) := by
  let _ := S.monoidal
  let _ := s
  change (𝟙 _ ⊗ₘ f) ≫ (β_ _ _).hom ≫ _ = ((β_ _ _).hom ≫ _) ≫ _
  rw [BraidedCategory.braiding_naturality_assoc]
  simpa only [WeilConjectures.CoefficientClosedStructure.tensor, tensor_map,
    Category.assoc] using
    congrArg ((β_ (H.obj (op P, O)) N).hom ≫ ·)
      (ringedSiteDualEvaluation_naturality S O u P f)

/-- The node's actual canonical comparison as a natural transformation.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualEvaluationLeftNatTrans (P : D) :
    Prod.sectR (H.obj (op P, O)) D ⋙ S.tensor ⟶ Prod.sectR (op P) D ⋙ H where
  app N := ringedSiteDualEvaluationLeft S s O u P N
  naturality _ _ f := ringedSiteDualEvaluationLeft_naturality S s O u P f

end Closed

section Site
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

/-- The coefficient sheaf regarded as a complex in degree zero.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnitComplex :=
  (HomologicalComplex.single (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
      (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))

/-- The coefficient object in the unbounded derived category.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityUnit
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))] :=
  DerivedCategory.Q.obj (ringedSiteDualityUnitComplex.{c, v, r} J R)

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))]

/-- A presentation of the existing derived tensor and Hom, normalized on K-flats.
The symmetry uses the Koszul sign. The right unitor is scalar multiplication;
the associator reassociates pure tensors. Together with models.uncurry_model these
conditions specify the evaluation constructions of 08JD and 0A97 on representatives.
Source: Stacks 06YN, 08JD, 0A97, 0A98
(blueprint: lem-sfb-ringed-site-duality-maps). -/
structure RingedSiteDualityModel where
  /-- The existing closed tensor-Hom structure. -/
  closed : WeilConjectures.CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{c, v, r, w} J R)
  /-- The existing pure-tensor normalization of its adjunction. -/
  models : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R closed
  /-- Symmetry of this same tensor structure. -/
  symmetric : @SymmetricCategory _ _ closed.monoidal
  /-- Identification of its tensor unit with the coefficient in degree zero. -/
  unitIso : closed.monoidal.tensorUnit ≅ ringedSiteDualityUnit.{c, v, r, w} J R
  /-- The ordinary coefficient complex is K-flat. -/
  unitKFlat : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
  /-- The symmetry descends the actual signed interchange of total-complex summands. -/
  symmetry_model : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P) (hQ :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q),
    ∃ σ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, P),
      (∀ (p q k : ℤ) (h : p + q = k) (h' : q + p = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        (σ.f k).val.app U (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q k h U x
      y) =
          (p * q).negOnePow • WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q P q p k h'
      U y x) ∧
      (models.iso J R closed P Q hP hQ).hom ≫
          (symmetric.braiding (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom =
        DerivedCategory.Q.map σ ≫ (models.iso J R closed Q P hQ hP).hom
  /-- The right unit constraint is induced by the actual scalar multiplication map. -/
  unit_model : ∀ (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) (hP :
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P),
    ∃ ρ : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      ringedSiteDualityUnitComplex.{c, v, r} J R) ⟶ P,
      (∀ (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U)
        (a : ((ringedSiteDualityUnitComplex.{c, v, r} J R).X 0).val.obj U),
        (ρ.f p).val.app U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      (ringedSiteDualityUnitComplex.{c, v, r} J R)
              p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (models.iso J R closed P (ringedSiteDualityUnitComplex.{c, v, r} J R)
          hP unitKFlat).hom ≫ closed.tensor.map (Prod.mkHom (𝟙 _) unitIso.inv) ≫
          (closed.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom = DerivedCategory.Q.map ρ
  /-- The associator descends the actual reassociation of total-complex summands. -/
  associator_model : ∀ (P Q V : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) P)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) Q)
      (hV : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) V),
    ∃ α : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q), V) ⟶
        (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P,
      (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)),
      (∀ (p q t i j k : ℤ) (hpq : p + q = i) (hit : i + t = k)
        (hqt : q + t = j) (hpj : p + j = k) (U : Cᵒᵖ)
        (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (V.X t).val.obj U),
        (α.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V i t k hit U
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P Q p q i hpq U x y) z) =
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P
      ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q, V)) p j k hpj U x
            (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R Q V q t j hqt U y z)) ∧
      (models.iso J R closed ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) V
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV).hom ≫
        closed.tensor.map (Prod.mkHom (models.iso J R closed P Q hP hQ).hom (𝟙 _)) ≫
        (closed.monoidal.associator (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
          (DerivedCategory.Q.obj V)).hom =
      DerivedCategory.Q.map α ≫
        (models.iso J R closed P ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (Q,
      V)) hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)).hom ≫
        closed.tensor.map (Prod.mkHom (𝟙 _) (models.iso J R closed Q V hQ hV).hom)

set_option Elab.async false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Canonical evaluation data exist without any perfectness hypothesis.
Source: Stacks 08JD, 0A97, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: descend total tensor on K-flats by site-derived-tensor descent, and derive the
ordinary componentwise tensor-Hom adjunction with a K-injective target. Its counit
has exactly the representative formula of CoefficientTensorModels. Descend the
ordinary scalar unit, reassociation, and signed interchange; their coherence
identities hold on pure tensor generators and hence after localization. The unit
is flat in degree zero. The formulas ringedSiteBidual and ringedSiteDualEvaluation
are respectively transposed signed evaluation and composition after the Hom-unit
identification. On ordinary Hom-computable representatives their components are
x ↦ (φ ↦ (-1)^{|x||φ|} φ(x)) and y tensor φ ↦ (x ↦ y φ(x)). These formulas commute
with slice restriction: restriction is exact, retains sections and the displayed
formulas, and commutes with K-flat tensor and K-injective Hom under the canonical
restriction comparisons. Naturality follows by transposing composite evaluations.
No isomorphism of either of these two maps is used or asserted. -/
theorem ringedSiteDualityMaps_exists : Nonempty (RingedSiteDualityModel.{c, v, r, w} J R) := by
  obtain ⟨S, T, β, ⟨K⟩⟩ := ringedDerived_closed_symmetric_monoidal.{c, v, r, w} J R
  have hunit : CochainComplex.IsKFlatIndependentCoefficients
      (J := J) (R := R) (ringedSiteDualityUnitComplex.{c, v, r} J R) := by
    intro F hF n
    exact (hF n).of_iso (HomologicalComplex.rightUnitor F).symm
  refine ⟨⟨S, T, β, K.unitIso, hunit, ?_, ?_, ?_⟩⟩
  · intro P Q hP hQ
    obtain ⟨s, hs, he⟩ := K.symmetry_model P Q hP hQ
    exact ⟨s.hom, hs, he⟩
  · intro P hP
    obtain ⟨ρ, hρ, he⟩ := K.rightUnitor_model P hP
    refine ⟨ρ.hom, ?_, ?_⟩
    · intro p U x a
      exact hρ p (Int.add_zero p) U a x
    · rw [K.tensorIso_both P (ringedTensorUnitComplex.{c, v, r} J R) hP hunit] at he
      exact he
  · intro P Q V hP hQ hV
    obtain ⟨α, hα, he⟩ := K.associator_model P Q V hP hQ hV
    refine ⟨α.hom, ?_, ?_⟩
    · intro p q t i j k hpq hit hqt hpj U x y z
      exact hα p q t i j k hpq hqt hit hpj U x y z
    · rw [K.tensorIso_both _ V
        (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ) hV,
        K.tensorIso_both P _ hP
          (WeilConjectures.coefficientTotalTensor_isKFlat.{r, c, v} J R Q V hQ hV)] at he
      exact he

attribute [local irreducible] homComplexFunctor homComplexπ

/-- The actual augmentation to the fixed K-injective replacement.
Source: Stacks 079P (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomAugmentation : 𝟭 _ ⟶ WeilConjectures.coefficientHomResolution.{r, c, v} J R :=
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r} J R).1
  CochainComplex.toKInjectiveResolution.{max c v r} _

/-- The action of the recorded Hom-complex bifunctor, with both variables explicit.
Source: Stacks 0A8X (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteHomComplexMap
    {E E' F F' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : E' ⟶ E) (g : F ⟶ F') :
    homComplex.{c, v, max c v r, max c v r} (R := R) E F ⟶
      homComplex.{c, v, max c v r, max c v r} (R := R) E' F' :=
  ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app F ≫
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op E')).map g

/-- Ordinary Hom to derived Hom, using the fixed augmentation and localization factorization.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomComparison (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    DerivedCategory.Q.obj (homComplex.{c, v, max c v r, max c v r} (R := R) E F) ⟶
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj
        (op (DerivedCategory.Q.obj E), DerivedCategory.Q.obj F) :=
  DerivedCategory.Q.map
    (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E) ((ringedSiteHomAugmentation.{c, v, r} J R).app F))
      ≫
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R E F).inv

/-- The ordinary comparison is invertible precisely when its augmentation Hom map is.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the factorization comparison is an isomorphism. Q inverts the displayed
quasi-isomorphism, so their composite is an isomorphism. -/
theorem ringedSiteOrdinaryHomComparison_isIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :
    IsIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F) := by
  let _ := h
  unfold ringedSiteOrdinaryHomComparison
  infer_instance

/-- The specified comparison iso when ordinary Hom computes derived Hom.
Source: Stacks 0A95 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryHomIso (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (h : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :=
  letI := ringedSiteOrdinaryHomComparison_isIso.{c, v, r, w} J R E F h
  asIso (ringedSiteOrdinaryHomComparison.{c, v, r, w} J R E F)

/-- Signed coefficient evaluation, specified on every localized Hom-product section.
Source: Stacks 0A97, 0A8X (blueprint: lem-sfb-ringed-site-duality-maps). -/
def RingedSiteBidualFormula (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (β : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R) (homComplex.{c, v, max c v r, max c v
      r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c,
      v, r} J R)) : Prop :=
  ∀ (i q : ℤ) (h : i + q = 0) (h' : q + i = 0) (U : Cᵒᵖ)
    (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj (op W.unop.left)),
    (((WeilConjectures.coefficientHomComponent.{r, c, v} J R (homComplex.{c, v, max c v r, max c v
      r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c,
      v, r} J R) i q 0 h').val.app U
      ((β.f i).val.app U x)).app W).hom φ =
      (i * q).negOnePow •
        (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R) q i 0 h).val.app (op W.unop.left) φ).app
          (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X i).val.map W.unop.hom.op x)

section OrdinaryBidualConstruction

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteDualityUnit_d (n m : ℤ) :
    (ringedSiteDualityUnitComplex.{c, v, r} J R).d n m = 0 := rfl

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteDualityUnit_isZero_X (t : ℤ) (ht : t ≠ 0) :
    IsZero ((ringedSiteDualityUnitComplex.{c, v, r} J R).X t) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ t ht

attribute [local irreducible] ringedSiteDualityUnitComplex

set_option backward.isDefEq.respectTransparency false

@[no_expose] private def ringedSiteEvalSection
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _))
    {U : Cᵒᵖ} (x : A.obj U) :
    (PresheafOfModules.restrictOver 𝒜 U.unop).obj (PresheafOfModules.homObj (R := 𝒜) A B) ⟶
      (PresheafOfModules.restrictOver 𝒜 U.unop).obj B where
  app W := ModuleCat.ofHom
    { toFun := fun φ ↦ (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
        (A.map W.unop.hom.op x)
      map_add' := by intros; rfl
      map_smul' := by
        intro a φ
        refine (PresheafOfModules.restrictOver_smul_app_apply a φ _ _).trans ?_
        change 𝒜.map (𝟙 (op W.unop.left)) a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x)) = a •
          ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
            (A.map W.unop.hom.op x))
        rw [𝒜.map_id]
        rfl }
  naturality {W W'} f := by
    ext φ
    change ((PresheafOfModules.restrictOverMap f.unop.left φ).app
        (op (Over.mk (𝟙 W'.unop.left)))).hom (A.map W'.unop.hom.op x) =
      B.map f.unop.left.op
        ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x))
    have hx : A.map f.unop.left.op (A.map W.unop.hom.op x) =
        A.map W'.unop.hom.op x := by
      rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
    exact (PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp _) _).trans
      ((congrArg (fun z ↦ (φ.app (op (Over.mk f.unop.left))).hom z) hx.symm).trans
        (PresheafOfModules.naturality_apply φ
          (Over.homMk f.unop.left (Category.comp_id _) :
            Over.mk f.unop.left ⟶ Over.mk (𝟙 W.unop.left)).op
              (A.map W.unop.hom.op x)))

@[no_expose] private def ringedSitePresheafBidual
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _)) :
    A ⟶ PresheafOfModules.homObj (R := 𝒜)
      (PresheafOfModules.homObj (R := 𝒜) A B) B where
      app U := ModuleCat.ofHom (R := 𝒜.obj U) (X := A.obj U)
        (Y := (PresheafOfModules.homObj (R := 𝒜)
          (PresheafOfModules.homObj (R := 𝒜) A B) B).obj U)
        { toFun := ringedSiteEvalSection.{c, v, r} 𝒜 A B
          map_add' := by
            intro x y
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (x + y)) =
              (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x) +
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op y)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              ((A.map W.unop.hom.op).hom.map_add x y)).trans
              (map_add (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom _ _)
          map_smul' := by
            intro a x
            apply PresheafOfModules.hom_ext
            intro W
            ext φ
            change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (a • x)) =
              𝒜.map W.unop.hom.op a •
                (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op x)
            exact (congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
              (A.map_smul W.unop.hom.op a x)).trans
              ((φ.app (op (Over.mk (𝟙 W.unop.left)))).hom.map_smul _ _) }
      naturality := by
        intro U V f
        ext x : 2
        apply PresheafOfModules.hom_ext
        intro W
        ext φ
        change (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map W.unop.hom.op (A.map f x)) =
          (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom (A.map (W.unop.hom ≫ f.unop).op x)
        exact congrArg (φ.app (op (Over.mk (𝟙 W.unop.left)))).hom
          (A.map_comp_apply f W.unop.hom.op x).symm


@[no_expose] private def ringedSiteSheafBidual
    (A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    A ⟶ SheafOfModules.homObj (R := R) (SheafOfModules.homObj (R := R) A B) B where
  val := ringedSitePresheafBidual.{c, v, r} R.obj A.val B.val

@[no_expose] private abbrev RingedSiteComplex := CochainComplex (SheafOfModules.{max c v r}
  ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ

@[no_expose] private def ringedSiteBidualComponent
    (E F : RingedSiteComplex.{c, v, r} J R) (i q : ℤ) :
    E.X i ⟶ SheafOfModules.homObj (R := R)
      ((homComplex.{c, v, max c v r, max c v r} (R := R) E F).X q) (F.X (q + i)) :=
  (i * q).negOnePow • (ringedSiteSheafBidual.{c, v, r} J R (E.X i) (F.X (q + i)) ≫
    SheafOfModules.homObjMap (R := R)
      (homComplexπ.{c, v, max c v r, max c v r} (R := R) E F q i (q + i)
        (Int.add_comm i q)) (𝟙 _))


@[no_expose] private def ringedSiteBidualDegree
    (E F : RingedSiteComplex.{c, v, r} J R) (i : ℤ) :
    E.X i ⟶ (homComplex.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E F) F).X i :=
  Fan.IsLimit.lift
    (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E F) F i)
    (ringedSiteBidualComponent.{c, v, r} J R E F i)


attribute [local irreducible] ringedSiteBidualComponent ringedSiteBidualDegree

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R))] in
private theorem ringedSiteBidualDegree_proj
    (E F : RingedSiteComplex.{c, v, r} J R) (i q : ℤ) :
    ringedSiteBidualDegree.{c, v, r} J R E F i ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E F) F i q (q + i) rfl =
      ringedSiteBidualComponent.{c, v, r} J R E F i q := by
  unfold ringedSiteBidualDegree
  exact Fan.IsLimit.fac
    (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E F) F i)
    (ringedSiteBidualComponent.{c, v, r} J R E F i) q

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R))] in
private theorem ringedSiteBidualDegree_eval
    (E F : RingedSiteComplex.{c, v, r} J R) (i q t : ℤ) (h : q + i = t)
    (U : Cᵒᵖ) (x : (E.X i).val.obj U) (W : (Over U.unop)ᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E F).X q).val.obj
      (op W.unop.left)) :
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E F) F i q t h).val.app U
        ((ringedSiteBidualDegree.{c, v, r} J R E F i).val.app U x)).app W).hom φ =
      (i * q).negOnePow •
        (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E F q i t
          ((Int.add_comm i q).trans h)).val.app (op W.unop.left) φ).app
            (op (Over.mk (𝟙 W.unop.left)))).hom
              ((E.X i).val.map W.unop.hom.op x) := by
  subst t
  let e : (E.X i ⟶ SheafOfModules.homObj (R := R)
      ((homComplex.{c, v, max c v r, max c v r} (R := R) E F).X q) (F.X (q + i))) →+
      (F.X (q + i)).val.obj (op W.unop.left) :=
    { toFun f := ((f.val.app U x).app W).hom φ
      map_zero' := rfl
      map_add' _ _ := rfl }
  have he := congrArg e (ringedSiteBidualDegree_proj.{c, v, r} J R E F i q)
  unfold ringedSiteBidualComponent at he
  simp only [Units.smul_def, map_zsmul] at he
  exact he


set_option backward.isDefEq.respectTransparency false


private theorem ringedSitePresheafHomObjMap_zero_target
    (𝒜 : Cᵒᵖ ⥤ CommRingCat.{max c v r})
    (A B B' : PresheafOfModules.{max c v r} (𝒜 ⋙ forget₂ _ _)) :
    PresheafOfModules.homObjMap (R := 𝒜) (𝟙 A) (0 : B ⟶ B') = 0 := by
  ext U φ : 3
  exact Limits.comp_zero (f := (PresheafOfModules.restrictOver 𝒜 U.unop).map (𝟙 A) ≫ φ)
    (Z := (PresheafOfModules.restrictOver 𝒜 U.unop).obj B')

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R))] in
private theorem ringedSiteHomObjMap_zero_target
    (A B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    SheafOfModules.homObjMap (R := R) (𝟙 A) (0 : B ⟶ B') = 0 := by
  apply SheafOfModules.hom_ext
  have hz (M N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
      (0 : M ⟶ N).val = (0 : M.val ⟶ N.val) :=
    (SheafOfModules.forget
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)).map_zero M N
  simp only [SheafOfModules.homObjMap_val, SheafOfModules.id_val, hz]
  exact ringedSitePresheafHomObjMap_zero_target.{c, v, r} R.obj A.val B.val B'.val


private theorem ringedSiteCompSub_zero {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟]
    {X Y Z : 𝒟} {a b : X ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : a = f ≫ g - b) (hg : g = 0) : a = -b := by
  rw [h, hg, comp_zero, zero_sub]

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteHomZero_d_proj
    (E F : RingedSiteComplex.{c, v, r} J R) (hF : ∀ n m, F.d n m = 0)
    (n m p t p' : ℤ)
    (hnm : n + 1 = m) (hpt : p + m = t) (hp' : p' + n = t) :
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
        F).d n m ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R) E
        F m p t hpt =
      -(n.negOnePow •
        (homComplexπ.{c, v, max c v r, max c v r} (R := R) E
          F n p' t hp' ≫
            SheafOfModules.homObjMap (R := R) (E.d p p') (𝟙 _))) := by
  have hd := homComplex_d_π.{c, v, max c v r, max c v r} (J := J) (R := R) E
    F n m p t (p + n) p' hnm hpt rfl hp'
  have hz : SheafOfModules.homObjMap (R := R) (𝟙 (E.X p))
      (F.d (p + n) t) = 0 := by
    rw [hF]
    exact ringedSiteHomObjMap_zero_target.{c, v, r} J R (E.X p) _ _
  exact ringedSiteCompSub_zero hd hz

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteHomZero_d_eval
    (E F : RingedSiteComplex.{c, v, r} J R) (hF : ∀ n m, F.d n m = 0)
    (n m p t p' : ℤ)
    (hnm : n + 1 = m) (hpt : p + m = t) (hp' : p' + n = t)
    (U : Cᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E
      F).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X p).val.obj (op W.unop.left)) :
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E
        F m p t hpt).val.app U
      (((homComplex.{c, v, max c v r, max c v r} (R := R) E
        F).d n m).val.app U φ)).app W).hom x =
      -n.negOnePow •
        ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E
          F n p' t hp').val.app U φ).app W).hom
            ((E.d p p').val.app (op W.unop.left) x)) := by
  let e : (((homComplex.{c, v, max c v r, max c v r} (R := R) E
      F).X n) ⟶
        SheafOfModules.homObj (R := R) (E.X p)
          (F.X t)) →+
        (F.X t).val.obj (op W.unop.left) :=
    { toFun f := ((f.val.app U φ).app W).hom x
      map_zero' := rfl
      map_add' _ _ := rfl }
  have he := congrArg e
    (ringedSiteHomZero_d_proj.{c, v, r} J R E F hF n m p t p' hnm hpt hp')
  simp only [map_neg, Units.smul_def, map_zsmul] at he
  exact he.trans (Units.neg_smul n.negOnePow _).symm

private theorem ringedSiteBidualSigns {G : Type*} [AddCommGroup G]
    (i q : ℤ) (b : G) :
    -i.negOnePow • ((i * (q + 1)).negOnePow • (-q.negOnePow • b)) =
      ((i + 1) * q).negOnePow • b := by
  rw [smul_smul, smul_smul]
  congr 1
  rw [mul_add, mul_one, add_mul, one_mul,
    Int.negOnePow_add, Int.negOnePow_add]
  simp only [neg_mul, mul_neg, neg_neg]
  calc
    i.negOnePow * ((i * q).negOnePow * i.negOnePow) * q.negOnePow =
        (i * q).negOnePow * (i.negOnePow * i.negOnePow) * q.negOnePow := by ac_rfl
    _ = (i * q).negOnePow * q.negOnePow := by rw [Int.units_mul_self, mul_one]

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteBidualDegree_comm
    (E : RingedSiteComplex.{c, v, r} J R) (i : ℤ) :
    ringedSiteBidualDegree.{c, v, r} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R) i ≫
      (homComplex.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E
          (ringedSiteDualityUnitComplex.{c, v, r} J R))
        (ringedSiteDualityUnitComplex.{c, v, r} J R)).d i (i + 1) =
      E.d i (i + 1) ≫ ringedSiteBidualDegree.{c, v, r} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R) (i + 1) := by
  apply Fan.IsLimit.hom_ext (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R))
    (ringedSiteDualityUnitComplex.{c, v, r} J R) (i + 1))
  intro q
  simp only [fan_mk_proj]
  apply SheafOfModules.hom_ext
  ext U x : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have ho := ringedSiteHomZero_d_eval.{c, v, r} J R
    (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R))
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (ringedSiteDualityUnit_d.{c, v, r} J R) i (i + 1) q (q + (i + 1)) (q + 1) rfl rfl (by omega)
    U ((ringedSiteBidualDegree.{c, v, r} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R) i).val.app U x) W φ
  have hl := ringedSiteBidualDegree_eval.{c, v, r} J R E
    (ringedSiteDualityUnitComplex.{c, v, r} J R) i (q + 1) (q + (i + 1))
    (by omega) U x W
    (((homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)).d q (q + 1)).val.app
        (op W.unop.left) φ)
  have hi := ringedSiteHomZero_d_eval.{c, v, r} J R E
    (ringedSiteDualityUnitComplex.{c, v, r} J R)
    (ringedSiteDualityUnit_d.{c, v, r} J R) q (q + 1) i
    (q + (i + 1)) (i + 1) rfl (by omega) (by omega) (op W.unop.left) φ
    (op (Over.mk (𝟙 W.unop.left))) ((E.X i).val.map W.unop.hom.op x)
  have hr := ringedSiteBidualDegree_eval.{c, v, r} J R E
    (ringedSiteDualityUnitComplex.{c, v, r} J R) (i + 1) q (q + (i + 1))
    rfl U ((E.d i (i + 1)).val.app U x) W φ
  have hx := PresheafOfModules.naturality_apply (E.d i (i + 1)).val W.unop.hom.op x
  rw [← hx] at hr
  exact ho.trans ((congrArg (fun z ↦ -i.negOnePow • z)
    (hl.trans (congrArg (fun z ↦ (i * (q + 1)).negOnePow • z) hi))).trans
      ((ringedSiteBidualSigns i q _).trans hr.symm))

omit [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj R))] in
private theorem ringedSiteHomObj_isZero_target
    (A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    (hB : IsZero B) : IsZero (SheafOfModules.homObj (R := R) A B) := by
  apply (IsZero.iff_id_eq_zero _).2
  rw [← SheafOfModules.homObjMap_id (R := R), hB.eq_of_src (𝟙 B) 0]
  exact ringedSiteHomObjMap_zero_target.{c, v, r} J R A B B

omit [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r}
      RingCat.{max c v r})).obj R))] in
private theorem ringedSiteBidualFormula_ext
    (E : RingedSiteComplex.{c, v, r} J R)
    (β γ : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E
        (ringedSiteDualityUnitComplex.{c, v, r} J R))
      (ringedSiteDualityUnitComplex.{c, v, r} J R))
    (hβ : RingedSiteBidualFormula.{c, v, r} J R E β)
    (hγ : RingedSiteBidualFormula.{c, v, r} J R E γ) : β = γ := by
  unfold RingedSiteBidualFormula at hβ hγ
  unfold WeilConjectures.coefficientHomComponent at hβ hγ
  apply HomologicalComplex.hom_ext
  intro i
  apply homComplex_hom_ext.{c, v, max c v r, max c v r}
  intro q t h
  by_cases ht : t = 0
  · rcases ht with rfl
    apply SheafOfModules.hom_ext
    ext U x : 3
    apply PresheafOfModules.hom_ext
    intro W
    ext φ
    have h' : i + q = 0 := by omega
    have hqi : q + i = 0 := by omega
    exact (hβ i q h' hqi U x W φ).trans (hγ i q h' hqi U x W φ).symm
  · exact (ringedSiteHomObj_isZero_target.{c, v, r} J R _ _
      (ringedSiteDualityUnit_isZero_X.{c, v, r} J R t ht)).eq_of_tgt _ _

/-- The ordinary signed evaluation chain map is uniquely determined by its section formula.
Source: Stacks 0A97, 0A8X (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: use the Hom-product universal property twice and evaluate each factor on
sections to define the degree maps. The Koszul sign is (-1)^(i*q). Expanding both
Hom differentials shows the two chain-map composites agree. All other target
components have nonzero coefficient degree and hence vanish. The same product
universal properties and sectionwise extensionality prove uniqueness. -/
theorem ringedSiteOrdinaryBidual_existsUnique (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ∃! β : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R) (homComplex.{c, v, max c v r, max c
      v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R))
      (ringedSiteDualityUnitComplex.{c, v, r} J R),
      RingedSiteBidualFormula.{c, v, r} J R E β := by
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  let β : E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E
        (ringedSiteDualityUnitComplex.{c, v, r} J R))
      (ringedSiteDualityUnitComplex.{c, v, r} J R) :=
    { f := fun i ↦ ringedSiteBidualDegree.{c, v, r} J R E
        (ringedSiteDualityUnitComplex.{c, v, r} J R) i
      comm' := by
        intro i j h
        change i + 1 = j at h
        subst j
        exact ringedSiteBidualDegree_comm.{c, v, r} J R E i }
  have hβ : RingedSiteBidualFormula.{c, v, r} J R E β := by
    intro i q h h' U x W φ
    exact ringedSiteBidualDegree_eval.{c, v, r} J R E
      (ringedSiteDualityUnitComplex.{c, v, r} J R) i q 0 h' U x W φ
  exact ⟨β, hβ, fun γ hγ ↦ ringedSiteBidualFormula_ext.{c, v, r} J R E γ β hγ hβ⟩

end OrdinaryBidualConstruction

/-- The actual ordinary signed bidual map, chosen from its unique section characterization.
Source: Stacks 0A97 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryBidual (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :=
  (ringedSiteOrdinaryBidual_existsUnique.{c, v, r} J R E).exists.choose

/-- Graded tensor-Hom evaluation, including its zero components.
Source: Stacks 08JE, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps). -/
def RingedSiteEvaluationFormula (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (F, homComplex.{c, v, max c v
      r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶ homComplex.{c, v,
      max c v r, max c v r} (R := R) E F) : Prop :=
  (∀ (p q k a : ℤ) (hpq : p + q = k) (haq : a + q = 0) (hak : a + k = p)
    (U : Cᵒᵖ) (y : (F.X p).val.obj U)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X a).val.obj (op W.unop.left)),
    (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a p hak).val.app U
        ((ε.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F (homComplex.{c, v, max c v r,
      max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) p q k hpq U y φ))).app
      W).hom x =
      (((WeilConjectures.coefficientHomComponent.{r, c, v} J R E (ringedSiteDualityUnitComplex.{c,
      v, r} J R) q a 0 haq).val.app U φ).app W).hom x •
        (F.X p).val.map W.unop.hom.op y) ∧
  (∀ (p q k a b : ℤ) (hpq : p + q = k) (hab : a + k = b) (_haq : a + q ≠ 0)
    (U : Cᵒᵖ) (y : (F.X p).val.obj U)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v,
      r} J R)).X q).val.obj U),
    (WeilConjectures.coefficientHomComponent.{r, c, v} J R E F k a b hab).val.app U
      ((ε.f k).val.app U
        (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R F (homComplex.{c, v, max c v r,
      max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) p q k hpq U y φ)) = 0)

/-- The ordinary evaluation chain map, uniquely specified on the actual tensor generators.
Source: Stacks 08JE, 0A98 (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: define every Hom-product projection on a total-tensor summand by the
specified sheaf-bilinear evaluation. Sheafification and the coproduct universal
property supply each degree map. The tensor and Hom differentials give the same
two terms, with the second sign (-1)^(p+q+1). Thus these are chain maps. Pure tensor
generators, Hom-product projections and sheaf separation give uniqueness. -/
theorem ringedSiteOrdinaryEvaluation_existsUnique (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ∃! ε : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (F, homComplex.{c, v, max c v
      r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J R)) ⟶ homComplex.{c, v,
      max c v r, max c v r} (R := R) E F,
      RingedSiteEvaluationFormula.{c, v, r} J R E F ε := by
  sorry

/-- Ordinary tensor-Hom evaluation, with real data fixed by its unique pure-tensor formula.
Source: Stacks 08JE (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteOrdinaryEvaluation (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :=
  (ringedSiteOrdinaryEvaluation_existsUnique.{c, v, r} J R E F).exists.choose

/-- Biduality is the signed ordinary map under the two specified Hom comparisons.
Source: Stacks 0A97, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: the closed transposition is pinned by models.uncurry_model. The normalized
symmetry supplies precisely the interchange sign. Apply this twice and use the
specified scalar unit. Localize the resulting ordinary chain map and its two
augmentation comparisons. The tensor-Hom adjunction identifies it with the
transpose that defines ringedSiteBidual; no K-flatness is needed for E or its dual. -/
theorem ringedSiteBidual_normalization (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hE : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J R))))
    (hD : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 (homComplex.{c, v, max c v r, max c v
      r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)))
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J
      R)))) :
    ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R)
        (DerivedCategory.Q.obj E) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E (ringedSiteDualityUnitComplex.{c,
      v, r} J R) hE).hom.op (𝟙 _)) =
    DerivedCategory.Q.map (ringedSiteOrdinaryBidual.{c, v, r} J R E) ≫
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R (homComplex.{c, v, max c v r, max c v r} (R := R)
      E (ringedSiteDualityUnitComplex.{c, v, r} J R)) (ringedSiteDualityUnitComplex.{c, v, r} J R)
      hD).hom := by
  sorry

/-- Evaluation is the unsigned ordinary map under the specified tensor and Hom comparisons.
Source: Stacks 08JE, 08JJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: transpose the comparison using the normalized tensor-Hom adjunction.
Associator normalization identifies its summand maps with ordinary composite
evaluation. Unit normalization gives y*phi(x), with no extra sign. Both tensor
arguments are K-flat, so models.iso is the specified tensor comparison. Localizing
the unique ordinary evaluation map gives the equation. The hypotheses are exactly
those required for the two augmentation comparisons to be invertible. -/
theorem ringedSiteDualEvaluation_normalization
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (E F : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hF : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R) F) (hD
      : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E (ringedSiteDualityUnitComplex.{c, v, r} J
      R)))
    (hE : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app (ringedSiteDualityUnitComplex.{c, v, r} J R))))
    (hEF : QuasiIso (ringedSiteHomComplexMap.{c, v, r} J R (𝟙 E)
      ((ringedSiteHomAugmentation.{c, v, r} J R).app F))) :
    (M.models.iso J R M.closed F (homComplex.{c, v, max c v r, max c v r} (R := R) E
      (ringedSiteDualityUnitComplex.{c, v, r} J R)) hF hD).hom ≫
      M.closed.tensor.map (Prod.mkHom (𝟙 _)
        (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E (ringedSiteDualityUnitComplex.{c, v, r} J R)
      hE).hom) ≫
      ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R)
        M.unitIso (DerivedCategory.Q.obj E) (DerivedCategory.Q.obj F) =
    DerivedCategory.Q.map (ringedSiteOrdinaryEvaluation.{c, v, r} J R E F) ≫
      (ringedSiteOrdinaryHomIso.{c, v, r, w} J R E F hEF).hom := by
  sorry

/-- Slice restriction sends zero maps to zero, by its sectionwise construction.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: overFunctor keeps the components of a module morphism and only restricts
its index category. Each component of a zero morphism remains zero. -/
theorem ringedSiteDualityRestriction_preservesZero (U : C) :
    (SheafOfModules.overFunctor.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
        U).PreservesZeroMorphisms := by
  classical
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  constructor
  intro X Y
  ext V x
  rfl

/-- Forgetting commutativity commutes with slice restriction as sheaves of rings.
Source: Stacks 03DJ (blueprint: lem-sfb-ringed-site-duality-maps).
Proof: both sides have the section ring R(V), and the same ring restriction map,
on an object V to U of the slice. Extensionality of ring sheaves gives equality;
the sheaf-condition proofs are propositionally irrelevant. -/
theorem ringedSiteDualityRestrictionCoefficient_eq (U : C) :
    (sheafCompose (J.over U)
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over U) =
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).over U := by
  have hSheaf : HasSheafify J AddCommGrpCat.{max c v r} := inferInstance
  have hW : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := inferInstance
  have hDerived : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :=
    inferInstance
  rfl

/-- The actual termwise restriction functor on complexes.
Source: Stacks 03DJ, 08FI (blueprint: lem-sfb-ringed-site-duality-maps). -/
def ringedSiteDualityRestrictionComplex (U : C) :=
  letI := ringedSiteDualityRestriction_preservesZero.{c, v, r} J R U
  ((SheafOfModules.overFunctor.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U) ⋙
      SheafOfModules.restrictScalars (eqToHom
        (ringedSiteDualityRestrictionCoefficient_eq.{c, v, r} J R U))).mapHomologicalComplex
          (ComplexShape.up ℤ)

/-- Canonical maps commute with exact slice restriction. The functor F is specified
by termwise restriction and localization. Its tensor and Hom comparisons are the
closed evaluation-compatible comparisons, not separate choices of bidual/evaluation
maps. The two equations state compatibility for the actual previously defined maps.
Source: Stacks 08JB, 08JD, 0A97, 0A98, 03DJ
(blueprint: lem-sfb-ringed-site-duality-maps).
Proof: exact module restriction inverts quasi-isomorphisms on complexes, hence
factors through Q with the displayed comparison. It preserves the ordinary unit
and sheafified tensor generators, so K-flat descent gives the tensor comparison.
Restriction preserves K-injectives and the actual Hom-product projections; the
fixed augmentation comparisons give the Hom comparison. These comparisons commute
with componentwise evaluation. Transpose this evaluation square, first after
signed interchange and then after composite evaluation, to obtain the bidual
and tensor-Hom squares. This proof does not assume perfectness. -/
theorem ringedSiteDualityMaps_restriction
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (U : C)
    [HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasDerivedCategory.{w'} (SheafOfModules.{max c v r}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj (R.over U)))]
    (MU : RingedSiteDualityModel.{max c v, v, r, w'} (J.over U) (R.over U)) :
    ∃ F : DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ⥤
      DerivedCategory (SheafOfModules.{max c v r}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r}
        RingCat.{max c v r})).obj (R.over U))),
      Nonempty (DerivedCategory.Q ⋙ F ≅
        ringedSiteDualityRestrictionComplex.{c, v, r} J R U ⋙ DerivedCategory.Q.{w'}) ∧
      ∃ (t : M.closed.tensor ⋙ F ≅ (F.prod F) ⋙ MU.closed.tensor)
        (h : (derivedInternalHomOfUniverses.{c, v, r, w} J R) ⋙ F ≅ (F.op.prod F) ⋙
      (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)))
        (o : F.obj (ringedSiteDualityUnit.{c, v, r, w} J R) ≅ ringedSiteDualityUnit.{max c v, v, r,
      w'} (J.over U) (R.over U)),
      (∀ P N,
        F.map (M.closed.evaluation P N) =
          t.hom.app ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P, N), P) ≫
            MU.closed.tensor.map (Prod.mkHom (h.hom.app (op P, N)) (𝟙 _)) ≫
              MU.closed.evaluation (F.obj P) (F.obj N)) ∧
      (∀ P,
        F.map (ringedSiteBidual M.closed M.symmetric (ringedSiteDualityUnit.{c, v, r, w} J R) P) ≫
          h.hom.app (op ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P,
      ringedSiteDualityUnit.{c, v, r, w} J R)), ringedSiteDualityUnit.{c, v, r, w} J R) ≫
          (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map (Prod.mkHom
            (h.inv.app (op P, ringedSiteDualityUnit.{c, v, r, w} J R)).op o.hom) ≫
          (derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map (Prod.mkHom
            ((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map
      (Prod.mkHom (𝟙 (op (F.obj P))) o.inv)).op (𝟙 _)) =
        ringedSiteBidual MU.closed MU.symmetric (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over
      U) (R.over U)) (F.obj P)) ∧
      (∀ P N,
        F.map (ringedSiteDualEvaluation M.closed (ringedSiteDualityUnit.{c, v, r, w} J R) M.unitIso
      P N) ≫
          h.hom.app (op P, N) =
        t.hom.app (N, (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op P,
      ringedSiteDualityUnit.{c, v, r, w} J R)) ≫
          MU.closed.tensor.map (Prod.mkHom (𝟙 _) (h.hom.app (op P, ringedSiteDualityUnit.{c, v, r,
      w} J R))) ≫
          MU.closed.tensor.map (Prod.mkHom (𝟙 _)
            ((derivedInternalHomOfUniverses.{max c v, v, r, w'} (J.over U) (R.over U)).map
      (Prod.mkHom (𝟙 (op (F.obj P))) o.hom))) ≫
          ringedSiteDualEvaluation MU.closed (ringedSiteDualityUnit.{max c v, v, r, w'} (J.over U)
      (R.over U)) MU.unitIso (F.obj P) (F.obj N)) := by
  sorry

end Site
end CategoryTheory
