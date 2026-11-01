/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.AlgebraicGeometry.StrictTower.ConstantNormalization.ConstantTowerDirectImageNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! # Reindexing of constant image evaluation

Source: Stacks 0D6E, 0E8I and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem evalR_comm (B : Type (u + 1)) [CommRing B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    evalR B f n = (Functor.rightDerivedFunctorCommIso
      (show towerDirectImage B f ⋙ (evaluation ℕᵒᵖ (Modules B Y)).obj (op n) ≅
        (evaluation ℕᵒᵖ (Modules B X)).obj (op n) ⋙ moduleDirectImage B f from
          Iso.refl _)).hom := by
  let V := (evaluation ℕᵒᵖ (Modules B Y)).obj (op n)
  let U := (evaluation ℕᵒᵖ (Modules B X)).obj (op n)
  let P := towerDirectImage B f
  let Q := moduleDirectImage B f
  let c : P ⋙ V ≅ U ⋙ Q := Iso.refl _
  have : PreservesFiniteLimits (towerPullback B f) := towerPullback_finiteLimits B f
  have : PreservesFiniteColimits (towerPullback B f) := towerPullback_finiteColimits B f
  have : PreservesFiniteLimits (modulePullback B f) := modulePullback_finiteLimits B f
  have : PreservesFiniteColimits (modulePullback B f) := modulePullback_finiteColimits B f
  let a : towerPullback B f ⊣ P :=
    (Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)).whiskerRight ℕᵒᵖ
  let a' : modulePullback B f ⊣ Q :=
    Scheme.proEtaleRingModuleAdjunction f (coefficients B Y)
      (coefficients B X) (constantRingIso B f)
  let s := (eqToIso (evaluationPullback B f n)).symm
  have h := ConstantNormalization.squareComparison_eq_mate P U V Q
    (towerPullback B f) (modulePullback B f) a a' s c (evaluation_mate B f n)
  have hs : ((Functor.mapDerivedCategoryCompIso V (modulePullback B f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso s ≪≫
        Functor.mapDerivedCategoryCompIso (towerPullback B f) U).hom =
      (evalG B f n).inv := by
    dsimp only [s, evalG]
    simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
    rfl
  rw [hs] at h
  exact h.symm

private theorem mapDerived_refl_inv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (Functor.mapDerivedCategoryNatIso (Iso.refl F)).inv = 𝟙 _ := by
  have h := Iso.inv_hom_id (Functor.mapDerivedCategoryNatIso (Iso.refl F))
  rw [Functor.mapDerivedCategoryNatIso_refl, Category.comp_id] at h
  exact h

private theorem proper_reindex_evaluation {X Y : Scheme.{u}} (g : X ⟶ Y)
    (e : ℕ) (he : 1 ≤ e) (n : ℕ)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((reindexProper l E g e he).inv.app N) ≫
      (subsequenceEvaluation l E Y e n).hom.app
        ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
      (evalR (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g
        (e * (n + 1) - 1)).app N =
    (evalR (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g n).app
        ((subsequence l E X e).obj N) ≫
      (moduleDirectImage
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).rightDerivedFunctor.map
         ((subsequenceEvaluation l E X e n).hom.app N) := by
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  have := subsequence_preservesKInjective l E X e he
  let VX := (evaluation ℕᵒᵖ (Modules B X)).obj (op n)
  let VY := (evaluation ℕᵒᵖ (Modules B Y)).obj (op n)
  let WX := (evaluation ℕᵒᵖ (Modules B X)).obj (op (e * (n + 1) - 1))
  let WY := (evaluation ℕᵒᵖ (Modules B Y)).obj (op (e * (n + 1) - 1))
  let c : towerDirectImage B g ⋙ VY ≅ VX ⋙ moduleDirectImage B g := Iso.refl _
  let d : towerDirectImage B g ⋙ WY ≅ WX ⋙ moduleDirectImage B g := Iso.refl _
  have h := Functor.rightDerivedFunctorCommIso_hom_app_comp
    c (reindexProperOrdinary l E g e) d (Iso.refl _) (Iso.refl _)
    (fun M ↦ by
      simp only [d, c, reindexProperOrdinary, Iso.refl_hom, Iso.refl_inv,
        NatTrans.id_app]
      erw [VY.map_id]
      repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
      rfl) N
  have hh : (evalR B g (e * (n + 1) - 1)).app N =
      (subsequenceEvaluation l E Y e n).inv.app ((R B g).obj N) ≫
        (ev B Y n).map ((reindexProper l E g e he).hom.app N) ≫
        (evalR B g n).app ((subsequence l E X e).obj N) ≫
        (moduleDirectImage B g).rightDerivedFunctor.map
          ((subsequenceEvaluation l E X e n).hom.app N) := by
    dsimp only [c, d, VX, VY, WX, WY] at h
    rw [← evalR_comm B g (e * (n + 1) - 1), ← evalR_comm B g n] at h
    simp only [mapDerived_refl_inv, Functor.mapDerivedCategoryNatIso_refl,
      Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, NatTrans.id_app,
      Category.comp_id, Category.assoc, subsequenceEvaluation,
      reindexProper, Functor.rightDerivedFunctorCommIso] at h ⊢
    repeat' first | erw [Category.id_comp] at h | erw [Category.comp_id] at h
    (convert h using 1; rfl)
  rw [hh]
  erw [Iso.hom_inv_id_app_assoc]
  erw [← (ev B Y n).map_comp_assoc, Iso.inv_hom_id_app,
    (ev B Y n).map_id, Category.id_comp]

private theorem open_reindex_evaluation {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (e n : ℕ)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((reindexOpen l E j e).inv.app N) ≫
      (subsequenceEvaluation l E Y e n).hom.app
        ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).obj N) ≫
      (evalJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j
        (e * (n + 1) - 1)).hom.app N =
    (evalJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j n).hom.app
        ((subsequence l E X e).obj N) ≫
      (moduleJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) j).mapDerivedCategory.map
         ((subsequenceEvaluation l E X e n).hom.app N) := by
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let VX := (evaluation ℕᵒᵖ (Modules B X)).obj (op n)
  let VY := (evaluation ℕᵒᵖ (Modules B Y)).obj (op n)
  let WX := (evaluation ℕᵒᵖ (Modules B X)).obj (op (e * (n + 1) - 1))
  let WY := (evaluation ℕᵒᵖ (Modules B Y)).obj (op (e * (n + 1) - 1))
  have h := Functor.exactSquare_comp_inverse
    (ordinarySubsequence l E X e) VX WX (ordinarySubsequence l E Y e) VY WY
    (towerJ B j) (towerJ B j) (moduleJ B j)
    (reindexOpenOrdinary l E j e) (eqToIso (evaluationOpen B j n))
    (eqToIso (evaluationOpen B j (e * (n + 1) - 1))) (Iso.refl _) (Iso.refl _)
    (fun M ↦ by
      simp only [reindexOpenOrdinary, eqToIso_refl, Iso.refl_hom,
        NatTrans.id_app]
      erw [VY.map_id, (moduleJ B j).map_id]
      repeat' erw [Category.id_comp]) N
  have hh : (evalJ B j (e * (n + 1) - 1)).hom.app N ≫
      (moduleJ B j).mapDerivedCategory.map ((subsequenceEvaluation l E X e n).inv.app N) =
      (subsequenceEvaluation l E Y e n).inv.app ((J B j).obj N) ≫
        (ev B Y n).map ((reindexOpen l E j e).hom.app N) ≫
        (evalJ B j n).hom.app ((subsequence l E X e).obj N) := by
    dsimp only [VX, VY, WX, WY] at h
    simp only [subsequenceEvaluation, evalJ, reindexOpen,
      Functor.mapDerivedCategorySquareIso, Iso.symm_inv, Iso.symm_hom,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, NatTrans.comp_app,
      Category.id_comp, Category.assoc] at h ⊢
    (convert h using 1; rfl)
  have ht := congrArg (fun t ↦
    (ev B Y n).map ((reindexOpen l E j e).inv.app N) ≫
      (subsequenceEvaluation l E Y e n).hom.app ((J B j).obj N) ≫ t ≫
      (moduleJ B j).mapDerivedCategory.map
        ((subsequenceEvaluation l E X e n).hom.app N)) hh
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc] at ht
  erw [(moduleJ B j).mapDerivedCategory.map_id, (ev B Y n).map_id] at ht
  repeat' first | erw [Category.id_comp] at ht | erw [Category.comp_id] at ht
  exact ht

/-- Evaluation at an arithmetic subsequence commutes with the constant proper/open
image comparison.
Source: Stacks 0D6E, 0E8I, 0940.
(blueprint: lem-pur-constant-image-reindex-evaluation).
Proof: for proper image the ordinary selection/evaluation square is the identity.
Both derived comparisons are characterized by the same right-derived unit, so
right-derived uniqueness identifies their composites. For open extension all
functors are exact and the two ordinary squares are identities; localization of
these equal squares is equal. Whisker the proper equality by the open functor,
whisker the open equality by proper image, and use naturality to compose them.
The retained index is e(n+1)-1, with no boundedness assumption. -/
theorem constantImage_reindexEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (e : ℕ) (hepos : 1 ≤ e) (n : ℕ)
    (N : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Y n).map
        ((reindexImage l E c e hepos).inv.app N) ≫
      (subsequenceEvaluation l E Y e n).hom.app ((image l E c).obj N) ≫
      (constantImageEvaluation l E c (e * (n + 1) - 1)).hom.app N =
      (constantImageEvaluation l E c n).hom.app ((subsequence l E X e).obj N) ≫
        (PurCompactSupport.image (constants l E) c).map
          ((subsequenceEvaluation l E X e n).hom.app N) := by
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  let Q := (moduleDirectImage B c.g).rightDerivedFunctor
  have hp := proper_reindex_evaluation l E c.g e hepos n ((J B c.i).obj N)
  have ho := open_reindex_evaluation l E c.i e n N
  dsimp only [reindexImage, constantImageEvaluation, Iso.trans_inv, Iso.trans_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, asIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [image, Functor.comp_obj]
  erw [reassoc_of% hp]
  have hn := (evalR B c.g n).naturality ((reindexOpen l E c.i e).inv.app N)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← Q.map_comp_assoc, ← Q.map_comp]
  simp only [Category.assoc]
  erw [ho]
  simp only [Q, Functor.map_comp]
  rfl

end WeilConjectures.PurStrictScalar
