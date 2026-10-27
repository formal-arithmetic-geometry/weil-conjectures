/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.CategoryTheory.AugmentedAlgebraTowerCompletionModel
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Adjunction.Limits
import all Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Sheaf.CategoryTheory.KFlatAugmentedRoosComparison

/-! # Canonical evaluation duality and augmented completion

Source: main-20261015/sec-six-functors-basics/sk-lem-int-tensor/
det-lem-int-tensor-product.proof.md, first paragraph; Stacks Tag 0FPU.
(blueprint: lem-sfb-evaluation-duality-completion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v u w z a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures

attribute [local instance 1000001] RingedDerivedNative.cachedCompose

namespace CategoryTheory.EvaluationDualityCompletion

-- Prefer the supplied sequential-limit structure to broad generic instance searches.
private local instance (priority := 10000) {A : Type a} [Category.{b} A]
    [HasLimitsOfShape ℕᵒᵖ A] (F : ℕᵒᵖ ⥤ A) : HasLimit F :=
  HasLimitsOfShape.has_limit F

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (ringedSiteModules.{max c v u, max c v u, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))]

/-- The evaluation-normalized closed native tensor, fixed by the dependency theorem.
Source: Stacks 08J9 (blueprint: lem-sfb-evaluation-duality-completion). -/
def closed := (RingedDerivedNative.closedAdjunction.{c, v, u, w} J R).choose

attribute [local irreducible] closed

/-- The dual object for a specified evaluation-normalized closed structure.
Source: Stacks 0FPU (blueprint: lem-sfb-evaluation-duality-completion). -/
def dual {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M : A) :=
  H.obj (op M, S.monoidal.tensorUnit)

/-- The canonical transpose of contraction with evaluation.
Source: Stacks 0FPU (blueprint: lem-sfb-evaluation-duality-completion). -/
abbrev comparison {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M N : A) :
    S.tensor.obj (N, dual S M) ⟶ H.obj (op M, N) :=
  CategoryTheory.ringedSiteDualEvaluation S S.monoidal.tensorUnit (Iso.refl _) M N

/-- Coevaluation is the inverse comparison applied to the transpose of the identity.
Source: Stacks 0FPU (blueprint: lem-sfb-evaluation-duality-completion). -/
def coevaluation {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M : A) (h : ∀ N, IsIso (comparison S M N)) :
    S.monoidal.tensorUnit ⟶ S.tensor.obj (M, dual S M) :=
  letI := S.monoidal
  S.transpose _ M M (λ_ M).hom ≫ @inv _ _ _ _ (comparison S M M) (h M)

private theorem first_triangle {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M : A)
    (h : ∀ N, IsIso (comparison S M N)) :
    letI := S.monoidal
    (λ_ M).inv ≫ coevaluation S M h ▷ M ≫ (α_ M (dual S M) M).hom ≫
      M ◁ S.evaluation M (𝟙_ _) ≫ (ρ_ M).hom = 𝟙 M := by
  let := S.monoidal
  let := h M
  have hc : coevaluation S M h ≫ comparison S M M =
      S.transpose _ M M (λ_ M).hom := by
    simp only [coevaluation, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have ht := congrArg ((S.transpose _ M M).symm) hc
  dsimp only [comparison, ringedSiteDualEvaluation, CoefficientClosedStructure.tensor,
    tensor_obj] at ht
  dsimp only [CoefficientClosedStructure.transpose] at ht
  erw [(S.adjunction M).homEquiv_naturality_left_symm] at ht
  dsimp only [dual, CoefficientClosedStructure.tensor, tensor_obj] at ht
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at ht
  change (coevaluation S M h ▷ M) ≫ _ = (λ_ M).hom at ht
  simpa only [dual, CoefficientClosedStructure.tensor, tensor_map, id_tensorHom,
    Iso.refl_inv, whiskerLeft_id, Category.id_comp, Category.comp_id,
    Category.assoc, Iso.inv_hom_id] using congrArg (fun f ↦ (λ_ M).inv ≫ f) ht

private theorem second_triangle {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M : A)
    (h : ∀ N, IsIso (comparison S M N)) :
    letI := S.monoidal
    (ρ_ (dual S M)).inv ≫ dual S M ◁ coevaluation S M h ≫
      (α_ (dual S M) M (dual S M)).inv ≫ S.evaluation M (𝟙_ _) ▷ dual S M ≫
      (λ_ (dual S M)).hom = 𝟙 (dual S M) := by
  let := S.monoidal
  let D := dual S M
  let c := coevaluation S M h
  let e := S.evaluation M (𝟙_ A)
  have zig := first_triangle S M h
  change (λ_ M).inv ≫ c ▷ M ≫ (α_ M D M).hom ≫ M ◁ e ≫ (ρ_ M).hom = 𝟙 M at zig
  apply (S.transpose D M (𝟙_ A)).symm.injective
  change (((ρ_ D).inv ≫ D ◁ c ≫ (α_ D M D).inv ≫ e ▷ D ≫
    (λ_ D).hom) ▷ M) ≫ e = (𝟙 D ▷ M) ≫ e
  rw [id_whiskerRight, Category.id_comp]
  calc
    _ = (ρ_ D).inv ▷ M ≫ (D ◁ c) ▷ M ≫ (α_ D M D).inv ▷ M ≫
        (α_ (D ⊗ M) D M).hom ≫ e ▷ (D ⊗ M) ≫ (λ_ (D ⊗ M)).hom ≫ e := by
      monoidal
    _ = (ρ_ D).inv ▷ M ≫ (D ◁ c) ▷ M ≫ (α_ D M D).inv ▷ M ≫
        (α_ (D ⊗ M) D M).hom ≫ (D ⊗ M) ◁ e ≫ (ρ_ (D ⊗ M)).hom ≫ e := by
      rw [whiskerRight_comp_leftUnitor_hom_comp]
      rfl
    _ = D ◁ ((λ_ M).inv ≫ c ▷ M ≫ (α_ M D M).hom ≫ M ◁ e ≫ (ρ_ M).hom) ≫ e := by
      monoidal
    _ = e := by rw [zig, whiskerLeft_id, Category.id_comp]

@[instance_reducible]
private def canonicalPairing {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (M : A)
    (h : ∀ N, IsIso (comparison S M N)) :
    letI := S.monoidal
    ExactPairing M (dual S M) := by
  let := S.monoidal
  exact
    { coevaluation' := coevaluation S M h
      evaluation' := S.evaluation M (𝟙_ A)
      evaluation_coevaluation' := by
        rw [← cancel_epi (λ_ M).inv, ← cancel_mono (ρ_ M).hom]
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id] using first_triangle S M h
      coevaluation_evaluation' := by
        rw [← cancel_epi (ρ_ (dual S M)).inv, ← cancel_mono (λ_ (dual S M)).hom]
        simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
          Category.comp_id] using second_triangle S M h }

private theorem dual_adjunctions {A : Type a} [Category.{b} A] {H : Aᵒᵖ × A ⥤ A}
    (S : CoefficientClosedStructure H) (s : @SymmetricCategory A _ S.monoidal)
    (M : A) (h : ∀ N, IsIso (comparison S M N)) :
    letI := S.monoidal
    Nonempty (tensorLeft M ⊣ tensorLeft (dual S M)) ∧
      Nonempty (tensorLeft (dual S M) ⊣ tensorLeft M) := by
  let := S.monoidal
  let := s
  let := canonicalPairing S M h
  refine ⟨⟨?_⟩, ⟨tensorLeftAdjunction M (dual S M)⟩⟩
  exact ((tensorRightAdjunction M (dual S M)).ofNatIsoLeft
    (BraidedCategory.tensorLeftIsoTensorRight M).symm).ofNatIsoRight
      (BraidedCategory.tensorLeftIsoTensorRight (dual S M)).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- All conclusions of canonical duality and augmented completion for the actual maps.
The monoidal instance is the evaluation-normalized native structure, rather than an
additional hypothesis. Source: Stacks 0FPU and 0941; first paragraph of the integral
 tensor-product proof (blueprint: lem-sfb-evaluation-duality-completion). -/
def Statement : Prop :=
  let S := closed.{c, v, u, w} J R
  letI := S.monoidal
  ∀ (M : DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
    (h : ∀ N, IsIso (comparison S M N)),
    let T := tensorLeft M
    (λ_ M).inv ≫ coevaluation S M h ▷ M ≫ (α_ M (dual S M) M).hom ≫
        M ◁ S.evaluation M (𝟙_ _) ≫ (ρ_ M).hom = 𝟙 M ∧
    (ρ_ (dual S M)).inv ≫ dual S M ◁ coevaluation S M h ≫
        (α_ (dual S M) M (dual S M)).inv ≫ S.evaluation M (𝟙_ _) ▷ dual S M ≫
        (λ_ (dual S M)).hom = 𝟙 (dual S M) ∧
    Nonempty (T ⊣ tensorLeft (dual S M)) ∧
    Nonempty (tensorLeft (dual S M) ⊣ T) ∧
    (∀ (I : Type z), PreservesLimitsOfShape (Discrete I) (T)) ∧
    (∀ (F : ℕᵒᵖ ⥤ DerivedCategory (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)))
      (s : Cone F), Pretriangulated.IsHomotopyLimit s →
        Pretriangulated.IsHomotopyLimit ((T).mapCone s)) ∧
    ∀ [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))],
      ∃ L : AugmentedTowerCompletion.RoosLimit
          (A := ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
      ∀ X : ℕᵒᵖ ⥤ CommMon (ringedSiteModules.{max c v u, max c v u, v, c}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)),
        Nonempty (AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit) ∧
        ∀ B : AugmentedTowerCompletion.Model
          (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R))
          (AugmentedTowerCompletion.algebraComplexes X)
          (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit,
        ∃ θ : B.completion ⋙ T ≅ T ⋙ B.completion,
          (∀ N, (T).map (B.unit.app N) ≫ θ.hom.app N =
            B.unit.app (T.obj N)) ∧
          (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (T.obj N)))

section NativeSetup
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private local instance : MonoidalCategory (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesMonoidal R
private local instance : SymmetricCategory (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesSymmetric R
private local instance : MonoidalPreadditive (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesPreadditive R
private local instance : MonoidalClosed (RingedDerivedNative.Modules.{c, v, u} J R) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
private local instance : IsGrothendieckAbelian.{max c v u}
    (RingedDerivedNative.Modules.{c, v, u} J R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1
private local instance : Abelian.HasFunctorialFlatResolution
    (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi R

private local instance : HasLimitsOfSize.{0, 0} (RingedDerivedNative.Modules.{c, v, u} J R) :=
  RingedDerivedNative.baseLimits.{c, v, u} J R
private local instance : HasColimitsOfSize.{0, 0} (RingedDerivedNative.Modules.{c, v, u} J R) :=
  RingedDerivedNative.baseColimits.{c, v, u} J R
private local instance (X Y : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    X.HasTensor Y := RingedDerivedNative.gradedTensor.{c, v, u} J R X Y
private local instance (W X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasTensor₄ObjExt W X Y Z :=
  RingedDerivedNative.gradedTensorFour.{c, v, u} J R W X Y Z
private local instance (X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  RingedDerivedNative.gradedTensorLeft.{c, v, u} J R X Y Z
private local instance (X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  RingedDerivedNative.gradedTensorRight.{c, v, u} J R X Y Z
private local instance (M : RingedDerivedNative.Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  RingedDerivedNative.auxTensorLeftColimits.{c, v, u} J R M
private local instance (M : RingedDerivedNative.Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  RingedDerivedNative.auxTensorRightColimits.{c, v, u} J R M

private local instance complexMonoidal : MonoidalCategory
    (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
  HomologicalComplex.monoidalCategory (RingedDerivedNative.Modules.{c, v, u} J R) (.up ℤ)

attribute [local instance 10000] MonoidalCategory.toMonoidalCategoryStruct

attribute [local irreducible] RingedDerivedNative.monoidal RingedDerivedNative.lax
  SheafOfModules.monoidalCategory

end NativeSetup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def coneOfRoosTriangle {A : Type a} [Category.{b} A]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (L : A) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op) L p δ) :
    Cone F where
  pt := L
  π := NatTrans.ofOpSequence (fun n ↦ p ≫ Pi.π _ n) (by
    intro n
    simp only [Functor.const_obj_map]
    have hzero := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT
    have hn := congrArg (fun f ↦ f ≫ Pi.π (fun n : ℕ ↦ F.obj (op n)) n) hzero
    simp only [zero_comp] at hn
    change (p ≫ towerTransitionEndomorphism
      (fun n ↦ F.map (homOfLE n.le_succ).op)) ≫ Pi.π _ n = 0 at hn
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Pi.lift_π, Preadditive.comp_sub, Category.assoc] at hn
    erw [Category.id_comp]
    simpa only [Category.assoc] using (sub_eq_zero.mp hn))

private theorem coneOfRoosTriangle_milnor {A : Type a} [Category.{b} A]
    [HasZeroObject A] [HasShift A ℤ] [Preadditive A]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (F : ℕᵒᵖ ⥤ A) [HasProduct (fun n : ℕ ↦ F.obj (op n))]
    (L : A) (p : L ⟶ ∏ᶜ fun n : ℕ ↦ F.obj (op n))
    (δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ L⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle (fun n ↦ F.map (homOfLE n.le_succ).op) L p δ) :
    Pretriangulated.IsHomotopyLimit (coneOfRoosTriangle F L p δ hT) := by
  let P : Fan (fun n : ℕ ↦ F.obj (op n)) := Fan.mk _ (Pi.π _)
  let hP : IsLimit P := productIsProduct _
  refine ⟨P, hP, δ, ?_⟩
  have hp : Fan.IsLimit.lift hP
      (fun n ↦ (coneOfRoosTriangle F L p δ hT).π.app (op n)) = p := by
    apply Pi.hom_ext
    intro n
    exact Fan.IsLimit.fac hP _ n
  have ht : Pretriangulated.towerShift (F := F) hP =
      towerProductShift (fun n ↦ F.map (homOfLE n.le_succ).op) := by
    apply Pi.hom_ext
    intro n
    change Pretriangulated.towerShift hP ≫ P.proj n = _
    rw [Pretriangulated.towerShift, Fan.IsLimit.fac]
    simp only [towerProductShift, Pi.lift_π]
    rfl
  rw [hp, ht]
  exact hT

private theorem roosLimit_exists
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R)] :
    Nonempty (AugmentedTowerCompletion.RoosLimit.{_, _, w}
      (A := RingedDerivedNative.Modules.{c, v, u} J R)) := by
  obtain ⟨RF, η, hRF, hI, _, hshift, hproducts, E, ε, p, δ, _, hT, _⟩ :=
    ringedStrictTowerHomotopyLimitIndependentCoefficients.{w, c, v, max c v u} J
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)
      (fun U a b ↦ @mul_comm (R.obj.obj U) inferInstance a b)
  let := hproducts
  exact ⟨{
    F := RF
    comparison := η
    universal := hRF
    computes := hI
    tower := E
    tower_comparison := ε
    cone := fun Z ↦ coneOfRoosTriangle (E.obj Z) (RF.obj Z) (p Z) (δ Z) (hT Z)
    point := fun _ ↦ rfl
    milnor := fun Z ↦ coneOfRoosTriangle_milnor (E.obj Z) (RF.obj Z) (p Z) (δ Z) (hT Z)
  }⟩

private def augmentationNatural {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X) :
    𝟭 (CochainComplex A ℤ) ⟶
      AugmentedTowerCompletion.tensorTower X ⋙ AugmentedTowerCompletion.ordinaryLimit where
  app P := AugmentedTowerCompletion.augmentationToLimit X α P
  naturality {P P'} f := by
    ext i : 1
    apply limit.hom_ext
    intro n
    simp only [Functor.id_map, HomologicalComplex.comp_f,
      AugmentedTowerCompletion.augmentationToLimit, Category.assoc,
      limit.lift_π, AugmentedTowerCompletion.ordinaryLimit,
      Functor.comp_map, Functor.mapHomologicalComplex_map_f, lim_map, limMap_π,
      limit.lift_π_assoc]
    dsimp only [AugmentedTowerCompletion.tensorTower,
      AugmentedTowerCompletion.transpose, Functor.comp_map,
      Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app, curriedTensor_map_app]
    simp only [← HomologicalComplex.comp_f]
    change (f ≫ (ρ_ P').inv ≫ P' ◁ α.app n).f i =
      ((ρ_ P).inv ≫ P ◁ α.app n ≫ f ▷ X.obj n).f i
    congr 1
    rw [rightUnitor_inv_naturality_assoc, whisker_exchange]

private theorem model_of_localization {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (K : ObjectProperty (CochainComplex A ℤ))
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (L : AugmentedTowerCompletion.DerivedLimit (A := A))
    [(K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage K.ι)]
    (hX : ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage K.ι).IsInvertedBy
      (K.ι ⋙ AugmentedTowerCompletion.tensorTower X ⋙ DerivedCategory.Q.{w} ⋙ L.F)) :
    Nonempty (AugmentedTowerCompletion.Model K X α L) := by
  let W := (HomologicalComplex.quasiIso A (.up ℤ)).inverseImage K.ι
  let q := K.ι ⋙ DerivedCategory.Q.{w}
  let F := K.ι ⋙ AugmentedTowerCompletion.tensorTower X ⋙ DerivedCategory.Q.{w} ⋙ L.F
  let F' := Localization.lift F hX q
  let e : q ⋙ F' ≅ F := Localization.fac F hX q
  let γ : q ⟶ F :=
    Functor.whiskerLeft K.ι
      (Functor.whiskerRight (augmentationNatural X α) DerivedCategory.Q ≫
        Functor.whiskerLeft (AugmentedTowerCompletion.tensorTower X) L.comparison)
  let τ : q ⋙ 𝟭 _ ⟶ q ⋙ F' := (Functor.rightUnitor q).hom ≫ γ ≫ e.inv
  let ff := Localization.fullyFaithfulWhiskeringLeft q W (DerivedCategory.{w} A)
  let η : 𝟭 _ ⟶ F' := ff.preimage τ
  have hη (P : K.FullSubcategory) : η.app (q.obj P) = τ.app P :=
    congr_app (ff.map_preimage τ) P
  refine ⟨{ completion := F', comparison := e, unit := η, unit_computes := ?_ }⟩
  intro P
  change η.app (q.obj P) ≫ e.hom.app P = _
  rw [hη]
  simp only [τ, γ, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  dsimp only [augmentationNatural]
  erw [Category.id_comp]
  rfl

private theorem tensorTower_map_quasiIso {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)]
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) {P P' : CochainComplex A ℤ} (f : P ⟶ P')
    (hf : ∀ n, QuasiIso (f ▷ X.obj n)) :
    QuasiIso ((AugmentedTowerCompletion.tensorTower X).map f) := by
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro n
  exact hf n

private theorem model_of_tensor_quasiIso {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (K : ObjectProperty (CochainComplex A ℤ))
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (L : AugmentedTowerCompletion.DerivedLimit (A := A))
    [(K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso A (.up ℤ)).inverseImage K.ι)]
    (hX : ∀ (P P' : CochainComplex A ℤ) (f : P ⟶ P'),
      K P → K P' → QuasiIso f → ∀ n, QuasiIso (f ▷ X.obj n)) :
    Nonempty (AugmentedTowerCompletion.Model K X α L) := by
  apply model_of_localization K X α L
  intro P P' f hf
  have hq : QuasiIso ((AugmentedTowerCompletion.tensorTower X).map (K.ι.map f)) :=
    tensorTower_map_quasiIso X f.hom (hX P.obj P'.obj f.hom P.property P'.property hf)
  have hi : IsIso (DerivedCategory.Q.{w}.map
      ((AugmentedTowerCompletion.tensorTower X).map (K.ι.map f))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso.{w}
      (φ := (AugmentedTowerCompletion.tensorTower X).map (K.ι.map f))).2 hq
  let := hi
  exact Functor.map_isIso L.F _

private theorem descend_completion_comparison
    {E : Type a} [Category.{b} E] {D : Type*} [Category D]
    (q : E ⥤ D) (W : MorphismProperty E) [q.IsLocalization W]
    (F T : D ⥤ D) (η : 𝟭 D ⟶ F)
    (e : q ⋙ F ⋙ T ≅ q ⋙ T ⋙ F)
    (he : ∀ P, T.map (η.app (q.obj P)) ≫ e.hom.app P = η.app (T.obj (q.obj P))) :
    ∃ θ : F ⋙ T ≅ T ⋙ F,
      (∀ N, T.map (η.app N) ≫ θ.hom.app N = η.app (T.obj N)) ∧
      (∀ N, IsIso (η.app N) → IsIso (η.app (T.obj N))) := by
  let ff := Localization.fullyFaithfulWhiskeringLeft q W D
  let θ : F ⋙ T ≅ T ⋙ F := ff.preimageIso e
  have ht (P : E) : θ.hom.app (q.obj P) = e.hom.app P :=
    congr_app (ff.map_preimage e.hom) P
  have h : ∀ N, T.map (η.app N) ≫ θ.hom.app N = η.app (T.obj N) := by
    have hh : (Functor.leftUnitor T).inv ≫ Functor.whiskerRight η T ≫ θ.hom =
        (Functor.rightUnitor T).inv ≫ Functor.whiskerLeft T η := by
      apply ff.map_injective
      ext P
      simpa only [Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
        NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_inv_app,
        Functor.whiskerRight_app, Category.id_comp, ht] using he P
    intro N
    simpa only [NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp] using congr_app hh N
  refine ⟨θ, h, ?_⟩
  intro N hN
  let := hN
  have hi : IsIso (T.map (η.app N) ≫ θ.hom.app N) := inferInstance
  rwa [h N] at hi

private theorem completion_transport
    {D : Type a} [Category.{b} D] (F T T' : D ⥤ D)
    (η : 𝟭 D ⟶ F) (d : T ≅ T')
    (θ' : F ⋙ T' ≅ T' ⋙ F)
    (h : ∀ N, T'.map (η.app N) ≫ θ'.hom.app N = η.app (T'.obj N)) :
    ∃ θ : F ⋙ T ≅ T ⋙ F,
      (∀ N, T.map (η.app N) ≫ θ.hom.app N = η.app (T.obj N)) ∧
      (∀ N, IsIso (η.app N) → IsIso (η.app (T.obj N))) := by
  let θ := Functor.isoWhiskerLeft F d ≪≫ θ' ≪≫ Functor.isoWhiskerRight d.symm F
  have hh (N) : T.map (η.app N) ≫ θ.hom.app N = η.app (T.obj N) := by
    dsimp only [θ, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    calc
      _ = d.hom.app N ≫ (T'.map (η.app N) ≫ θ'.hom.app N) ≫
          F.map (d.inv.app N) := by
        rw [d.hom.naturality_assoc]
        simp only [Category.assoc, Functor.id_obj]
      _ = d.hom.app N ≫ η.app (T'.obj N) ≫ F.map (d.inv.app N) := by rw [h]
      _ = η.app (T.obj N) := by
        rw [← η.naturality (d.inv.app N)]
        simp
  refine ⟨θ, hh, ?_⟩
  intro N hN
  let := hN
  have hi : IsIso (T.map (η.app N) ≫ θ.hom.app N) := inferInstance
  rwa [hh N] at hi

section LimitComparison
variable {B : Type a} [Category.{b} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]

private def limitModelCone (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) : Cone Z.asFunctor where
  pt := AugmentedTowerCompletion.ordinaryLimit.obj Z
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app Z
      naturality := by
        intro n m f
        ext i
        change 𝟙 (limit (Z.X i)) ≫ limit.π (Z.X i) m =
          limit.π (Z.X i) n ≫ (Z.X i).map f
        rw [Category.id_comp, limit.w] }

private def limitModelLimit (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    IsLimit (limitModelCone Z) :=
  HomologicalComplex.isLimitOfEval _ _ (fun i ↦ limit.isLimit (Z.X i))

private def limitModelPointIso (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    AugmentedTowerCompletion.ordinaryLimit.obj Z ≅ limit Z.asFunctor :=
  (limitModelLimit Z).conePointUniqueUpToIso (limit.isLimit Z.asFunctor)

private theorem limitModelPointIso_hom_π (Z : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (n : ℕᵒᵖ) :
    (limitModelPointIso Z).hom ≫ limit.π Z.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app Z :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit Z) (limit.isLimit Z.asFunctor) n

private def limitModelIso :
    AugmentedTowerCompletion.ordinaryLimit (A := B) ≅ roosLimitFunctor :=
  NatIso.ofComponents (fun Z ↦ limitModelPointIso Z) (by
    intro Z W f
    apply limit.hom_ext (F := W.asFunctor)
    intro n
    change (_ ≫ (limitModelPointIso W).hom) ≫ limit.π W.asFunctor n =
      ((limitModelPointIso Z).hom ≫
        lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)) ≫
          limit.π W.asFunctor n
    simp only [Category.assoc]
    rw [limitModelPointIso_hom_π, lim_map]
    erw [limMap_π]
    rw [← Category.assoc, limitModelPointIso_hom_π]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

variable [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

private def roosUnit (L : AugmentedTowerCompletion.DerivedLimit (A := B)) :
    roosLimitFunctor ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ L.F :=
  Functor.whiskerRight limitModelIso.inv DerivedCategory.Q ≫ L.comparison

private theorem roosUniversal (L : AugmentedTowerCompletion.DerivedLimit (A := B)) :
    L.F.IsRightDerivedFunctor (roosUnit L) (HomologicalComplex.quasiIso _ (.up ℤ)) := by
  let := L.universal
  have := Functor.IsRightDerivedFunctor.isLeftKanExtension L.F L.comparison
    (HomologicalComplex.quasiIso _ (.up ℤ))
  constructor
  apply (Functor.isLeftKanExtension_iff_of_iso₂ L.comparison (roosUnit L)
    (Functor.isoWhiskerRight limitModelIso DerivedCategory.Q) (Iso.refl L.F) ?_).1
  · infer_instance
  · ext Z
    simp only [roosUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.refl_hom, NatTrans.id_app,
      Functor.isoWhiskerRight_hom, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, Category.id_comp]
    exact Category.comp_id _

end LimitComparison

private def augmentationCone {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)]
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (P : CochainComplex A ℤ) : Cone ((AugmentedTowerCompletion.tensorTower X).obj P).asFunctor where
  pt := P
  π :=
    { app := fun n ↦ (ρ_ P).inv ≫ P ◁ α.app n
      naturality := by
        intro n m f
        change 𝟙 P ≫ _ = _ ≫ P ◁ X.map f
        rw [Category.id_comp, Category.assoc, ← whiskerLeft_comp]
        congr 2
        have hα := α.naturality f
        change 𝟙 _ ≫ α.app m = α.app n ≫ X.map f at hα
        exact (Category.id_comp _).symm.trans hα }

private theorem augmentationCone_lift {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (P : CochainComplex A ℤ) :
    limit.lift ((AugmentedTowerCompletion.tensorTower X).obj P).asFunctor
        (augmentationCone X α P) =
      AugmentedTowerCompletion.augmentationToLimit X α P ≫
        (limitModelIso.app ((AugmentedTowerCompletion.tensorTower X).obj P)).hom := by
  apply limit.hom_ext
  intro n
  rw [limit.lift_π, Category.assoc]
  dsimp only [limitModelIso, NatIso.ofComponents]
  erw [limitModelPointIso_hom_π]
  ext i
  symm
  apply limit.lift_π

private def strictAssociate {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)]
    (B : CochainComplex A ℤ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    tensorLeft B ⋙ AugmentedTowerCompletion.tensorTower X ≅
      AugmentedTowerCompletion.tensorTower X ⋙ KFlatAugmentedRoos.tower (tensorLeft B) :=
  NatIso.ofComponents (fun P ↦ by
    let e : X ⋙ tensorLeft (B ⊗ P) ≅ X ⋙ tensorLeft P ⋙ tensorLeft B :=
      NatIso.ofComponents (fun n ↦ α_ B P (X.obj n)) (by
        intro n m f
        exact associator_naturality_right B P (X.map f))
    exact AugmentedTowerCompletion.transpose.mapIso e) (by
    intro P P' f
    ext i n
    exact congrArg (fun g ↦ g.f i) (associator_naturality_middle B f (X.obj n)))

private theorem augmentation_tensor_lift {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    (B P : CochainComplex A ℤ) (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X) :
    limit.lift ((KFlatAugmentedRoos.tower (tensorLeft B)).obj
        ((AugmentedTowerCompletion.tensorTower X).obj P)).asFunctor
        ((tensorLeft B).mapCone (augmentationCone X α P)) ≫
        roosLimitFunctor.map ((strictAssociate B X).inv.app P) =
      limit.lift ((AugmentedTowerCompletion.tensorTower X).obj (B ⊗ P)).asFunctor
        (augmentationCone X α (B ⊗ P)) := by
  apply limit.hom_ext
  intro n
  dsimp only [roosLimitFunctor, Functor.comp_map]
  rw [Category.assoc, lim_map, limMap_π]
  dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex,
    Functor.comp_obj]
  erw [limit.lift_π_assoc, limit.lift_π]
  change (B ◁ ((ρ_ P).inv ≫ P ◁ α.app n)) ≫ (α_ B P (X.obj n)).inv =
    (ρ_ (B ⊗ P)).inv ≫ (B ⊗ P) ◁ α.app n
  monoidal

private theorem augmentation_roosUnit {A : Type a} [Category.{b} A] [Abelian A]
    [MonoidalCategory (CochainComplex A ℤ)] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    (L : AugmentedTowerCompletion.DerivedLimit (A := A))
    (X : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex A ℤ)) ⟶ X)
    (P : CochainComplex A ℤ) :
    DerivedCategory.Q.{w}.map
        (limit.lift ((AugmentedTowerCompletion.tensorTower X).obj P).asFunctor
          (augmentationCone X α P)) ≫
        (roosUnit L).app ((AugmentedTowerCompletion.tensorTower X).obj P) =
      DerivedCategory.Q.map (AugmentedTowerCompletion.augmentationToLimit X α P) ≫
        L.comparison.app ((AugmentedTowerCompletion.tensorTower X).obj P) := by
  rw [augmentationCone_lift]
  dsimp only [roosUnit, NatTrans.comp_app, Functor.whiskerRight_app]
  change DerivedCategory.Q.map
      (AugmentedTowerCompletion.augmentationToLimit X α P ≫
        (limitModelIso.app _).hom) ≫ DerivedCategory.Q.map (limitModelIso.app _).inv ≫
        L.comparison.app _ = _
  rw [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem roos_comparison_of_iso {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasCountableProducts (DerivedCategory.{w} A)]
    (F : CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (L : AugmentedTowerCompletion.DerivedLimit (A := A))
    (T : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A)
    (e : DerivedCategory.Q.{w} ⋙ T ≅ F ⋙ DerivedCategory.Q.{w})
    (β : DerivedCategory.Q.{w} ⋙ L.F ⋙ T ⟶
      KFlatAugmentedRoos.tower F ⋙ DerivedCategory.Q.{w} ⋙ L.F)
    (hi : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      IsIso (piComparison T (fun n : ℕ ↦ DerivedCategory.Q.obj (X.asFunctor.obj (op n)))) →
        IsIso (β.app X))
    (haug : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (δ : Cone X.asFunctor),
      T.map (DerivedCategory.Q.map (limit.lift X.asFunctor δ) ≫ (roosUnit L).app X) ≫
        β.app X = e.hom.app δ.pt ≫ DerivedCategory.Q.map
          (limit.lift ((KFlatAugmentedRoos.tower F).obj X).asFunctor (F.mapCone δ)) ≫
          (roosUnit L).app ((KFlatAugmentedRoos.tower F).obj X))
    (T' : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A)
    (μ : DerivedCategory.Q.{w} ⋙ T' ≅ F ⋙ DerivedCategory.Q.{w})
    (hp : PreservesLimitsOfShape (Discrete ℕ) T') :
    ∃ γ : DerivedCategory.Q.{w} ⋙ L.F ⋙ T' ≅
        KFlatAugmentedRoos.tower F ⋙ DerivedCategory.Q.{w} ⋙ L.F,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (δ : Cone X.asFunctor),
        T'.map (DerivedCategory.Q.map (limit.lift X.asFunctor δ) ≫ (roosUnit L).app X) ≫
          γ.hom.app X = μ.hom.app δ.pt ≫ DerivedCategory.Q.map
            (limit.lift ((KFlatAugmentedRoos.tower F).obj X).asFunctor (F.mapCone δ)) ≫
            (roosUnit L).app ((KFlatAugmentedRoos.tower F).obj X) := by
  let := hp
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q.{w}
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory.{w} A)
  let d : T' ≅ T := ff.preimageIso (μ ≪≫ e.symm)
  have hd (U : CochainComplex A ℤ) :
      d.hom.app (DerivedCategory.Q.obj U) ≫ e.hom.app U = μ.hom.app U := by
    have hh := congr_app (ff.map_preimage (μ ≪≫ e.symm).hom) U
    change d.hom.app (DerivedCategory.Q.obj U) = μ.hom.app U ≫ e.inv.app U at hh
    rw [hh, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  let := preservesLimitsOfShape_of_natIso (J := Discrete ℕ) d
  let (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (β.app X) := hi X inferInstance
  let γ := Functor.whiskerLeft (DerivedCategory.Q ⋙ L.F) d.hom ≫ β
  let (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : IsIso (γ.app X) := by
    dsimp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  let : IsIso γ := NatIso.isIso_of_isIso_app γ
  refine ⟨asIso γ, ?_⟩
  intro X δ
  change _ ≫ (d.hom.app _ ≫ β.app X) = _
  erw [← Category.assoc, d.hom.naturality, Category.assoc, haug X δ]
  rw [← Category.assoc, hd]

private theorem completion_of_roos_comparison
    {D : Type a} [Category.{b} D] [Abelian D]
    [MonoidalCategory (CochainComplex D ℤ)] [HasLimitsOfShape ℕᵒᵖ D]
    [HasDerivedCategory.{w} D] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ D)]
    (K : ObjectProperty (CochainComplex D ℤ))
    [(K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso D (.up ℤ)).inverseImage K.ι)]
    (L : AugmentedTowerCompletion.DerivedLimit (A := D))
    (A : CochainComplex D ℤ) (hA : ∀ P, K P → K (A ⊗ P))
    (T : DerivedCategory.{w} D ⥤ DerivedCategory.{w} D)
    (μ : DerivedCategory.Q.{w} ⋙ T ≅ tensorLeft A ⋙ DerivedCategory.Q.{w})
    (β : DerivedCategory.Q.{w} ⋙ L.F ⋙ T ≅
      KFlatAugmentedRoos.tower (tensorLeft A) ⋙ DerivedCategory.Q.{w} ⋙ L.F)
    (hβ : ∀ (Z : CochainComplex (ℕᵒᵖ ⥤ D) ℤ) (δ : Cone Z.asFunctor),
      T.map (DerivedCategory.Q.map (limit.lift Z.asFunctor δ) ≫ (roosUnit L).app Z) ≫
        β.hom.app Z = μ.hom.app δ.pt ≫ DerivedCategory.Q.map
          (limit.lift ((KFlatAugmentedRoos.tower (tensorLeft A)).obj Z).asFunctor
            ((tensorLeft A).mapCone δ)) ≫
          (roosUnit L).app ((KFlatAugmentedRoos.tower (tensorLeft A)).obj Z))
    (X : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (α : (Functor.const ℕᵒᵖ).obj (𝟙_ (CochainComplex D ℤ)) ⟶ X)
    (B : AugmentedTowerCompletion.Model K X α L) :
    ∃ θ : B.completion ⋙ T ≅ T ⋙ B.completion,
      (∀ N, T.map (B.unit.app N) ≫ θ.hom.app N = B.unit.app (T.obj N)) ∧
      (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (T.obj N))) := by
  let q := K.ι ⋙ DerivedCategory.Q.{w}
  let k := ObjectProperty.lift K (K.ι ⋙ tensorLeft A) (fun P ↦ hA P.obj P.property)
  let e : q ⋙ B.completion ⋙ T ≅ q ⋙ T ⋙ B.completion :=
    Functor.isoWhiskerRight B.comparison T ≪≫
      Functor.isoWhiskerLeft (K.ι ⋙ AugmentedTowerCompletion.tensorTower X) β ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft K.ι (strictAssociate A X).symm)
        (DerivedCategory.Q.{w} ⋙ L.F) ≪≫
      Functor.isoWhiskerLeft k B.comparison.symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft K.ι μ.symm) B.completion
  apply descend_completion_comparison q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage K.ι)
    B.completion T B.unit e
  intro P
  apply (cancel_mono
    (B.completion.map (μ.hom.app P.obj) ≫ B.comparison.hom.app (k.obj P))).1
  dsimp only [e, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [ObjectProperty.ι_obj, Functor.comp_obj]
  simp only [Category.assoc, ← B.completion.map_comp_assoc, Iso.inv_hom_id_app]
  erw [B.completion.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  change T.map (B.unit.app (q.obj P)) ≫
      T.map (B.comparison.hom.app P) ≫ β.hom.app _ ≫
        L.F.map (DerivedCategory.Q.map ((strictAssociate A X).inv.app P.obj)) =
    B.unit.app (T.obj (q.obj P)) ≫ B.completion.map (μ.hom.app P.obj) ≫
      B.comparison.hom.app (k.obj P)
  erw [← B.unit.naturality_assoc (μ.hom.app P.obj)]
  change T.map (B.unit.app (q.obj P)) ≫
      T.map (B.comparison.hom.app P) ≫ β.hom.app _ ≫
        L.F.map (DerivedCategory.Q.map ((strictAssociate A X).inv.app P.obj)) =
    μ.hom.app P.obj ≫ B.unit.app (q.obj (k.obj P)) ≫ B.comparison.hom.app (k.obj P)
  dsimp only [q, Functor.comp_obj, ObjectProperty.ι_obj]
  erw [← T.map_comp_assoc, B.unit_computes, B.unit_computes]
  erw [← augmentation_roosUnit L X α P.obj]
  erw [← Category.assoc, hβ _ (augmentationCone X α P.obj)]
  simp only [Category.assoc]
  change μ.hom.app P.obj ≫ _ = μ.hom.app P.obj ≫ _
  apply (cancel_epi (μ.hom.app P.obj)).2
  erw [← (roosUnit L).naturality ((strictAssociate A X).inv.app P.obj)]
  simp only [Functor.comp_map]
  rw [← DerivedCategory.Q.map_comp_assoc, augmentation_tensor_lift]
  exact augmentation_roosUnit L X α (A ⊗ P.obj)

private theorem completion_of_representatives
    {D : Type a} [Category.{b} D] [Abelian D] [HasDerivedCategory.{w} D]
    [MonoidalCategory (DerivedCategory.{w} D)]
    (K : ObjectProperty (CochainComplex D ℤ))
    [(K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso D (.up ℤ)).inverseImage K.ι)]
    (F : DerivedCategory.{w} D ⥤ DerivedCategory.{w} D) (η : 𝟭 _ ⟶ F)
    (h : ∀ P : K.FullSubcategory,
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft (DerivedCategory.Q.obj P.obj)) →
      ∃ θ : F ⋙ tensorLeft (DerivedCategory.Q.obj P.obj) ≅
          tensorLeft (DerivedCategory.Q.obj P.obj) ⋙ F,
        ∀ N, (tensorLeft (DerivedCategory.Q.obj P.obj)).map (η.app N) ≫ θ.hom.app N =
          η.app ((tensorLeft (DerivedCategory.Q.obj P.obj)).obj N))
    (M : DerivedCategory.{w} D)
    (hp : PreservesLimitsOfShape (Discrete ℕ) (tensorLeft M)) :
    let T := tensorLeft M
    ∃ θ : F ⋙ T ≅ T ⋙ F,
      (∀ N, T.map (η.app N) ≫ θ.hom.app N = η.app (T.obj N)) ∧
      (∀ N, IsIso (η.app N) → IsIso (η.app (T.obj N))) := by
  let := hp
  let q := K.ι ⋙ DerivedCategory.Q.{w}
  have := Localization.essSurj q
    ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage K.ι)
  let P := q.objPreimage M
  let i := q.objObjPreimageIso M
  let d : tensorLeft M ≅ tensorLeft (DerivedCategory.Q.obj P.obj) :=
    (curriedTensor _).mapIso i.symm
  let := preservesLimitsOfShape_of_natIso (J := Discrete ℕ) d
  obtain ⟨θ, hθ⟩ := h P inferInstance
  exact completion_transport F _ _ η d θ hθ

section NativeExactness
private local instance : MonoidalCategory (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesMonoidal R
private local instance : SymmetricCategory (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesSymmetric R
private local instance : MonoidalPreadditive (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.cochainModulesPreadditive R
private local instance : MonoidalClosed (RingedDerivedNative.Modules.{c, v, u} J R) :=
  (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
private local instance : IsGrothendieckAbelian.{max c v u}
    (RingedDerivedNative.Modules.{c, v, u} J R) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
    J R).1
private local instance : Abelian.HasFunctorialFlatResolution
    (RingedDerivedNative.Modules.{c, v, u} J R) :=
  SheafOfModules.hasFunctorialFlatResolution_kfi R

private local instance : HasLimitsOfSize.{0, 0} (RingedDerivedNative.Modules.{c, v, u} J R) :=
  RingedDerivedNative.baseLimits.{c, v, u} J R
private local instance : HasColimitsOfSize.{0, 0} (RingedDerivedNative.Modules.{c, v, u} J R) :=
  RingedDerivedNative.baseColimits.{c, v, u} J R
private local instance (X Y : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    X.HasTensor Y := RingedDerivedNative.gradedTensor.{c, v, u} J R X Y
private local instance (W X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasTensor₄ObjExt W X Y Z :=
  RingedDerivedNative.gradedTensorFour.{c, v, u} J R W X Y Z
private local instance (X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  RingedDerivedNative.gradedTensorLeft.{c, v, u} J R X Y Z
private local instance (X Y Z : GradedObject ℤ (RingedDerivedNative.Modules.{c, v, u} J R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  RingedDerivedNative.gradedTensorRight.{c, v, u} J R X Y Z
private local instance (M : RingedDerivedNative.Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  RingedDerivedNative.auxTensorLeftColimits.{c, v, u} J R M
private local instance (M : RingedDerivedNative.Modules.{c, v, u} J R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  RingedDerivedNative.auxTensorRightColimits.{c, v, u} J R M

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private local instance : MonoidalCategory
    (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
  complexMonoidal.{c, v, u} J R
attribute [local instance 10000] MonoidalCategory.toMonoidalCategoryStruct
attribute [local irreducible] RingedDerivedNative.monoidal RingedDerivedNative.lax
  SheafOfModules.monoidalCategory

private theorem native_tensor_map_quasiIso
    (P P' L : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (f : P ⟶ P')
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) P)
    (hP' : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) P')
    (hf : QuasiIso f) :
    letI := complexMonoidal.{c, v, u} J R
    QuasiIso (f ▷ L) := by
  let := complexMonoidal.{c, v, u} J R
  let := RingedDerivedNative.monoidal.{c, v, u, w} J R
  let := RingedDerivedNative.lax.{c, v, u, w} J R
  let := RingedDerivedNative.isIso_mu.{c, v, u, w} J R P L (Or.inl hP)
  let := RingedDerivedNative.isIso_mu.{c, v, u, w} J R P' L (Or.inl hP')
  let := hf
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso.{w} (φ := f ▷ L)).1
  have he : DerivedCategory.Q.{w}.map (f ▷ L) =
      inv (Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P L) ≫
        (DerivedCategory.Q.{w}.map f ▷ DerivedCategory.Q.{w}.obj L) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Q.{w} P' L := by
    rw [Functor.LaxMonoidal.μ_natural_left, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

private theorem native_model_exists
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R)]
    (X : ℕᵒᵖ ⥤ CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    : letI := complexMonoidal.{c, v, u} J R
    ∀ (α : (Functor.const ℕᵒᵖ).obj
      (𝟙_ (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)) ⟶ X)
    (L : AugmentedTowerCompletion.DerivedLimit
      (A := RingedDerivedNative.Modules.{c, v, u} J R)),
    Nonempty (AugmentedTowerCompletion.Model
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
        (J := J) (R := R)) X α L) := by
  let := complexMonoidal.{c, v, u} J R
  intro α L
  let K : ObjectProperty (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R)
  have : (K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage K.ι) := by
    change (coefficientKFlatInclusion.{u, c, v} J R ⋙ DerivedCategory.Q.{w}).IsLocalization _
    exact RingedDerivedNative.kFlatLocalization.{c, v, u, w} J R
  exact model_of_tensor_quasiIso K X α L (fun P P' f hP hP' hf n ↦
    native_tensor_map_quasiIso.{c, v, u, w} J R P P' (X.obj n) f hP hP' hf)

omit [HasDerivedCategory.{w} (ringedSiteModules.{max c v u, max c v u, v, c}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R))] in
private theorem native_tensor_kFlat
    (A P : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) A)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) P) :
    letI := complexMonoidal.{c, v, u} J R
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) (A ⊗ P) := by
  let := complexMonoidal.{c, v, u} J R
  rw [← RingedDerivedNative.totalTensor_eq.{c, v, u} J R A P]
  exact coefficientTotalTensor_isKFlat.{u, c, v} J R A P hA hP

private def nativeTensorComparison
    (A : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R) A) :
    letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
    DerivedCategory.Q.{w} ⋙ tensorLeft (DerivedCategory.Q.obj A) ≅
      tensorLeft A ⋙ DerivedCategory.Q.{w} := by
  let := RingedDerivedNative.monoidal.{c, v, u, w} J R
  let := RingedDerivedNative.lax.{c, v, u, w} J R
  let (P : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
    RingedDerivedNative.isIso_mu.{c, v, u, w} J R A P (Or.inl hA)
  exact NatIso.ofComponents
    (fun P ↦ asIso (Functor.LaxMonoidal.μ DerivedCategory.Q A P))
    (fun f ↦ Functor.LaxMonoidal.μ_natural_right DerivedCategory.Q A f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem native_roos_comparison
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R)]
    (L : AugmentedTowerCompletion.DerivedLimit
      (A := RingedDerivedNative.Modules.{c, v, u} J R))
    (A : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
      (J := J) (R := R) A)
    (hp : letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft (DerivedCategory.Q.{w}.obj A))) :
    letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
    ∃ β : DerivedCategory.Q.{w} ⋙ L.F ⋙ tensorLeft (DerivedCategory.Q.obj A) ≅
        KFlatAugmentedRoos.tower (tensorLeft A) ⋙ DerivedCategory.Q.{w} ⋙ L.F,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
        (γ : Cone X.asFunctor),
        (tensorLeft (DerivedCategory.Q.obj A)).map
            (DerivedCategory.Q.map (limit.lift X.asFunctor γ) ≫ (roosUnit L).app X) ≫
            β.hom.app X =
          (nativeTensorComparison.{c, v, u, w} J R A hA).hom.app γ.pt ≫
            DerivedCategory.Q.map
              (limit.lift ((KFlatAugmentedRoos.tower (tensorLeft A)).obj X).asFunctor
                ((tensorLeft A).mapCone γ)) ≫
              (roosUnit L).app ((KFlatAugmentedRoos.tower (tensorLeft A)).obj X) := by
  let := RingedDerivedNative.monoidal.{c, v, u, w} J R
  let := hp
  obtain ⟨products, T, e, β, μ, hexact, hres, hμ, hnat, hq, hf, hiso, haug⟩ :=
    kFlatAugmentedRoosComparison J R L.F (roosUnit L) (roosUniversal L)
  let := products
  let K : {P : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ //
      CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
        (J := J) (R := R) P} := ⟨A, hA⟩
  exact roos_comparison_of_iso (tensorLeft A) L (T K) (e K) (β K) (hiso K)
    (haug K) (tensorLeft (DerivedCategory.Q.obj A))
    (nativeTensorComparison.{c, v, u, w} J R A hA) hp

private theorem native_completion_representative
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R)]
    (L : AugmentedTowerCompletion.DerivedLimit
      (A := RingedDerivedNative.Modules.{c, v, u} J R))
    (A : CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (hA : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
      (J := J) (R := R) A)
    (hp : letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft (DerivedCategory.Q.{w}.obj A)))
    (X : ℕᵒᵖ ⥤ CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (α : (Functor.const ℕᵒᵖ).obj
      (𝟙_ (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)) ⟶ X)
    (B : AugmentedTowerCompletion.Model
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
        (J := J) (R := R)) X α L) :
    letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
    let T := tensorLeft (DerivedCategory.Q.obj A)
    ∃ θ : B.completion ⋙ T ≅ T ⋙ B.completion,
      (∀ N, T.map (B.unit.app N) ≫ θ.hom.app N = B.unit.app (T.obj N)) ∧
      (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (T.obj N))) := by
  let := RingedDerivedNative.monoidal.{c, v, u, w} J R
  let K : ObjectProperty (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R)
  let q := K.ι ⋙ DerivedCategory.Q.{w}
  have : q.IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage K.ι) :=
    RingedDerivedNative.kFlatLocalization.{c, v, u, w} J R
  obtain ⟨β, hβ⟩ := native_roos_comparison.{c, v, u, w} J R L A hA hp
  exact completion_of_roos_comparison K L A
    (fun P hP ↦ native_tensor_kFlat.{c, v, u} J R A P hA hP)
    (tensorLeft (DerivedCategory.Q.obj A))
    (nativeTensorComparison.{c, v, u, w} J R A hA) β hβ X α B

attribute [local irreducible] sheafCompose

private theorem native_completion
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ RingedDerivedNative.Modules.{c, v, u} J R)]
    (M : DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J R))
    (hp : letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft M))
    (L : AugmentedTowerCompletion.DerivedLimit
      (A := RingedDerivedNative.Modules.{c, v, u} J R))
    (X : ℕᵒᵖ ⥤ CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)
    (α : (Functor.const ℕᵒᵖ).obj
      (𝟙_ (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ)) ⟶ X)
    (B : AugmentedTowerCompletion.Model
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
        (J := J) (R := R)) X α L) :
    letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
    let T := tensorLeft M
    ∃ θ : B.completion ⋙ T ≅ T ⋙ B.completion,
      (∀ N, T.map (B.unit.app N) ≫ θ.hom.app N = B.unit.app (T.obj N)) ∧
      (∀ N, IsIso (B.unit.app N) → IsIso (B.unit.app (T.obj N))) := by
  let K : ObjectProperty (CochainComplex (RingedDerivedNative.Modules.{c, v, u} J R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u} (J := J) (R := R)
  have : (K.ι ⋙ DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage K.ι) :=
    RingedDerivedNative.kFlatLocalization.{c, v, u, w} J R
  let := RingedDerivedNative.monoidal.{c, v, u, w} J R
  have h (P : K.FullSubcategory)
      (hP : PreservesLimitsOfShape (Discrete ℕ)
        (tensorLeft (DerivedCategory.Q.{w}.obj P.obj))) :=
    (native_completion_representative.{c, v, u, w} J R L P.obj P.property hP X α B)
  exact completion_of_representatives
    (D := RingedDerivedNative.Modules.{c, v, u} J R) K B.completion B.unit
    (fun P hP ↦ ⟨(h P hP).choose, (h P hP).choose_spec.1⟩) M hp

private theorem native_homotopy_limit
    (M : DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J R))
    (hp : letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft M)) :
    letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
    ∀ (F : ℕᵒᵖ ⥤ DerivedCategory (RingedDerivedNative.Modules.{c, v, u} J R))
      (s : Cone F), Pretriangulated.IsHomotopyLimit s →
        Pretriangulated.IsHomotopyLimit ((tensorLeft M).mapCone s) := by
  unfold RingedDerivedNative.monoidal at hp ⊢
  let := hp
  intro F s hs
  exact hs.map (tensorLeft M)

end NativeExactness

/-- Canonical evaluation and coevaluation obey both triangles, give both tensor
adjunctions, preserve existing products and all sequential Milnor cones, and exchange
augmented algebra-tower completion including its actual canonical unit.

Source: first paragraph of det-lem-int-tensor-product.proof.md; Stacks 0FPU.
(blueprint: lem-sfb-evaluation-duality-completion).

Proof plan:
1. Transpose the definition of coevaluation under lem-sf-ringed-derived-tensor-hom-adjunction.
Injectivity of its Hom equivalence proves the M triangle.
2. Contract the proposed D triangle with evaluation. Interchange the two evaluations
on D tensor M tensor D tensor M and use step 1. Currying identifies the two sides
with that D endomorphism and its identity, proving the second triangle.
3. Apply lem-sfb-dual-tensor-adjunctions and symmetry to obtain both adjunctions.
The right-adjoint structure preserves every existing product, including the empty one.
4. The native derived tensor has the proved shift and triangulated instances.
Apply lem-pc-homotopy-limit-map using the product preservation from step 3.
K-flat localization is supplied by the native closed-adjunction construction.
5. Resolve N by a K-flat P. The strict augmented tower P tensor B_n computes the
specified derived tower by lem-sf-ringed-derived-native-tensor, including its unit.
Use lem-sfb-kflat-augmented-roos-comparison on a K-flat representative of M.
6. Reassociate A tensor (P tensor B_n) to (A tensor P) tensor B_n on strict complexes.
This identifies transitions and augmentations, including the zero shifted-product
coordinate. The normalized Roos comparison gives the natural isomorphism below
and the equality of whole completion-unit maps, not merely their projections.
7. Functors and composition preserve isomorphisms, so the unit equation proves
preservation of complete objects. Principal quotients and finite coefficient
reductions are special cases; no regularity or flatness of the quotients is used. -/
theorem evaluation_duality_completion : Statement.{c, v, u, w, z} J R := by
  let := SheafOfModules.cochainModulesMonoidal R
  let := complexMonoidal.{c, v, u} J R
  let S := closed.{c, v, u, w} J R
  have hm : S.monoidal = RingedDerivedNative.monoidal.{c, v, u, w} J R := by
    simpa only [S, closed] using
      (RingedDerivedNative.closedAdjunction.{c, v, u, w} J R).choose_spec.1
  let s : @SymmetricCategory _ _ S.monoidal :=
    hm.symm ▸ RingedDerivedNative.symmetric.{c, v, u, w} J R
  let := S.monoidal
  intro M h
  obtain ⟨hleft, hright⟩ := dual_adjunctions S s M h
  let adj := hright.some
  have hp (I : Type z) : PreservesLimitsOfShape (Discrete I) (tensorLeft M) :=
    adj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  have hpNative : letI := RingedDerivedNative.monoidal.{c, v, u, w} J R
      PreservesLimitsOfShape (Discrete ℕ) (tensorLeft M) :=
    hm ▸ adj.rightAdjoint_preservesLimits.preservesLimitsOfShape
  refine ⟨first_triangle S M h, second_triangle S M h, hleft, hright, hp, ?_, ?_⟩
  · exact hm.symm ▸ native_homotopy_limit J R M hpNative
  · intro inst
    obtain ⟨L⟩ := roosLimit_exists.{c, v, u, w} J R
    refine ⟨L, ?_⟩
    intro X
    refine ⟨native_model_exists.{c, v, u, w} J R
      (AugmentedTowerCompletion.algebraComplexes X)
      (AugmentedTowerCompletion.algebraAugmentation X) L.toDerivedLimit, ?_⟩
    intro B
    exact hm.symm ▸ native_completion.{c, v, u, w} J R M hpNative L.toDerivedLimit
      (AugmentedTowerCompletion.algebraComplexes X)
      (AugmentedTowerCompletion.algebraAugmentation X) B

end CategoryTheory.EvaluationDualityCompletion
