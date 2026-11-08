/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import Submission.WeilConjectures.Algebra.Homology.Coefficient.CoefficientLevelOrdinaryImages
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Adjunction.Additive

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Ordinary geometric images of strict coefficient systems

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w d a b c e av bv cv ev
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

private theorem transition_transpose_iff
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
    {Fm : A ⥤ C} {Gm : C ⥤ A} {Fn : B ⥤ D} {Gn : D ⥤ B}
    {RY : B ⥤ A} {RX : D ⥤ C} (am : Fm ⊣ Gm) (an : Fn ⊣ Gn)
    (β : RY ⋙ Fm ≅ Fn ⋙ RX) (δ : RX ⋙ Gm ≅ Gn ⋙ RY)
    (ht : ∀ M N (f : Fn.obj M ⟶ N),
      am.homEquiv _ _ (β.hom.app M ≫ RX.map f) =
        RY.map (an.homEquiv _ _ f) ≫ δ.inv.app N)
    {Mm : A} {Mn : B} {Nm : C} {Nn : D}
    (tM : Mm ⟶ RY.obj Mn) (tN : Nm ⟶ RX.obj Nn)
    (fm : Fm.obj Mm ⟶ Nm) (fn : Fn.obj Mn ⟶ Nn) :
    (fm ≫ tN = Fm.map tM ≫ β.hom.app Mn ≫ RX.map fn) ↔
      am.homEquiv _ _ fm ≫ Gm.map tN ≫ δ.hom.app Nn =
        tM ≫ RY.map (an.homEquiv _ _ fn) := by
  have he : am.homEquiv _ _ (Fm.map tM ≫ β.hom.app Mn ≫ RX.map fn) =
      tM ≫ RY.map (an.homEquiv _ _ fn) ≫ δ.inv.app Nn := by
    rw [am.homEquiv_naturality_left, ht]
  constructor
  · intro h
    have h' := congrArg (am.homEquiv _ _) h
    rw [am.homEquiv_naturality_right, he] at h'
    apply (cancel_mono (δ.inv.app Nn)).mp
    simpa [Category.assoc] using h'
  · intro h
    apply (am.homEquiv _ _).injective
    rw [am.homEquiv_naturality_right, he]
    have h' := congrArg (· ≫ δ.inv.app Nn) h
    simpa [Category.assoc] using h'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

omit [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [EssentiallySmall.{w} C] in
private theorem system_hom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def systemInverse
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    CoefficientSystem (J := J) O ell ⥤ CoefficientSystem (J := K) O ell where
  obj M := {
    level := fun n ↦ (S.lift n).modules.obj (M.level n)
    transition := fun n ↦ (S.lift (n + 1)).modules.map (M.transition n) ≫
      (S.restrictInverse (Nat.le_succ n)).hom.app (M.level n) }
  map {M N} f := {
    app := fun n ↦ (S.lift n).modules.map (f.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, f.comm, Functor.map_comp, Category.assoc]
      exact congrArg ((S.lift (n + 1)).modules.map (M.transition n) ≫ ·)
        ((S.restrictInverse (Nat.le_succ n)).hom.naturality (f.app n)) }
  map_id M := by
    apply system_hom_ext O ell
    funext n
    exact (S.lift n).modules.map_id _
  map_comp f g := by
    apply system_hom_ext O ell
    funext n
    exact (S.lift n).modules.map_comp _ _

private def systemDirect
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    CoefficientSystem (J := K) O ell ⥤ CoefficientSystem (J := J) O ell where
  obj M := {
    level := fun n ↦ (S.right n).obj (M.level n)
    transition := fun n ↦ (S.right (n + 1)).map (M.transition n) ≫
      (S.restrictRight (Nat.le_succ n)).hom.app (M.level n) }
  map {M N} f := {
    app := fun n ↦ (S.right n).map (f.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, f.comm, Functor.map_comp, Category.assoc]
      exact congrArg ((S.right (n + 1)).map (M.transition n) ≫ ·)
        ((S.restrictRight (Nat.le_succ n)).hom.naturality (f.app n)) }
  map_id M := by
    apply system_hom_ext O ell
    funext n
    exact (S.right n).map_id _
  map_comp f g := by
    apply system_hom_ext O ell
    funext n
    exact (S.right n).map_comp _ _

private def systemHomEquiv
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj)
    (M : CoefficientSystem (J := J) O ell) (N : CoefficientSystem (J := K) O ell) :
    ((systemInverse O ell L V adj S).obj M ⟶ N) ≃
      (M ⟶ (systemDirect O ell L V adj S).obj N) where
  toFun f := {
    app := fun n ↦ (S.levelAdj n).homEquiv _ _ (f.app n)
    comm := by
      intro n
      exact (transition_transpose_iff (S.levelAdj (n + 1)) (S.levelAdj n)
        (S.restrictInverse (Nat.le_succ n)) (S.restrictRight (Nat.le_succ n))
        (S.restrictTranspose (Nat.le_succ n)) (M.transition n) (N.transition n)
        (f.app (n + 1)) (f.app n)).1 (f.comm n) }
  invFun f := {
    app := fun n ↦ ((S.levelAdj n).homEquiv _ _).symm (f.app n)
    comm := by
      intro n
      dsimp only [systemDirect] at f
      apply (transition_transpose_iff (S.levelAdj (n + 1)) (S.levelAdj n)
        (S.restrictInverse (Nat.le_succ n)) (S.restrictRight (Nat.le_succ n))
        (S.restrictTranspose (Nat.le_succ n)) (M.transition n) (N.transition n)
        (((S.levelAdj (n + 1)).homEquiv _ _).symm (f.app (n + 1)))
        (((S.levelAdj n).homEquiv _ _).symm (f.app n))).2
      simpa only [Equiv.apply_symm_apply] using f.comm n }
  left_inv f := by
    apply system_hom_ext O ell
    funext n
    exact Equiv.symm_apply_apply _ _
  right_inv f := by
    apply system_hom_ext O ell
    funext n
    exact Equiv.apply_symm_apply _ _

private def systemAdjunction
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    systemInverse O ell L V adj S ⊣ systemDirect O ell L V adj S :=
  Adjunction.mkOfHomEquiv {
    homEquiv := systemHomEquiv O ell L V adj S
    homEquiv_naturality_left_symm := by
      intro M M' N f g
      apply system_hom_ext O ell
      funext n
      exact (S.levelAdj n).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := by
      intro M N N' f g
      apply system_hom_ext O ell
      funext n
      exact (S.levelAdj n).homEquiv_naturality_right _ _ }

private instance systemInverse_additive
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    (systemInverse O ell L V adj S).Additive where
  map_add {M N} f g := by
    apply system_hom_ext O ell
    funext n
    change (S.lift n).modules.map
      ((coefficientEvaluation (J := J) n).map (f + g)) =
      (coefficientEvaluation (J := K) n).map
        ((systemInverse O ell L V adj S).map f + (systemInverse O ell L V adj S).map g)
    simp only [Functor.map_add]
    rfl

private instance systemDirect_additive
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    (systemDirect O ell L V adj S).Additive :=
  (systemAdjunction O ell L V adj S).right_adjoint_additive

end SheafOfModules
