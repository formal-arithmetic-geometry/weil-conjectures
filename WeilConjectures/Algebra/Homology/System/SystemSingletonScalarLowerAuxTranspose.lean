/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarLowerAuxTransition

/-! # Transposes of the singleton coefficient comparisons

Transposes of the two composites in the lower-singleton compatibility across the composite
adjunction of scalar extension, singleton extension and sequence scalar extension.
Source: Stacks 0FND and 09T5; Zheng, Construction 4.1
(blueprint: lem-pur-system-singleton-scalar-lower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)

/-- The scalar associator square transposes to the two exact restriction compositors.
Source: Stacks 06YT and 0FND (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: both associators are left-adjoint uniqueness maps; their transposes are the units of
the composite-ring adjunction, up to the exact restriction compositors. -/
theorem singletonScalarSquare_transpose {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) (Z : DerivedCategory (systemLevel D n))
    (k : (systemDerivedTensor S D h).obj ((S (a.app (op m))).model.T.obj P) ⟶ Z) :
    (S (B.map (homOfLE h).op)).adjunction.homEquiv _ _
        ((S (a.app (op n))).adjunction.homEquiv _ _
          ((singletonScalarSquare S a n m h).hom.app P ≫ k)) =
      (S (a.app (op m))).adjunction.homEquiv _ _
          ((S (D.map (homOfLE h).op)).adjunction.homEquiv _ _ k) ≫
        (Functor.exactDerivedRestrictionComposition _ _ _
          (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
            (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op))).hom.app Z ≫
        (Functor.exactDerivedRestrictionComposition _ _ _
          (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
            (B.map (homOfLE h).op ≫ a.app (op n)) rfl)).inv.app Z := by
  simp only [singletonScalarSquare, systemScalarModelDerivedComposition, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Adjunction.leftAdjointUniq_inv_app]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  set δ₁ := Functor.exactDerivedRestrictionComposition _ _ _
    (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
      (B.map (homOfLE h).op ≫ a.app (op n)) rfl)
  set δ₂ := Functor.exactDerivedRestrictionComposition _ _ _
    (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
      (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op))
  have h₁ := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((S (B.map (homOfLE h).op)).adjunction.comp (S (a.app (op n))).adjunction).ofNatIsoRight δ₁)
    (S (B.map (homOfLE h).op ≫ a.app (op n))).adjunction P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h₁
  erw [Equiv.trans_apply] at h₁
  have h₂ := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (S (B.map (homOfLE h).op ≫ a.app (op n))).adjunction
    (((S (a.app (op m))).adjunction.comp (S (D.map (homOfLE h).op)).adjunction).ofNatIsoRight δ₂)
    P
  have hX : (S (B.map (homOfLE h).op)).adjunction.homEquiv _ _
      ((S (a.app (op n))).adjunction.homEquiv _ _
        ((Adjunction.leftAdjointUniq (((S (B.map (homOfLE h).op)).adjunction.comp
          (S (a.app (op n))).adjunction).ofNatIsoRight δ₁)
          (S (B.map (homOfLE h).op ≫ a.app (op n))).adjunction).hom.app P)) =
      (S (B.map (homOfLE h).op ≫ a.app (op n))).adjunction.unit.app P ≫ δ₁.inv.app _ := by
    rw [← h₁]
    simp
  rw [hX]
  have nat := δ₁.inv.naturality
    ((Adjunction.leftAdjointUniq (S (B.map (homOfLE h).op ≫ a.app (op n))).adjunction
      (((S (a.app (op m))).adjunction.comp (S (D.map (homOfLE h).op)).adjunction).ofNatIsoRight
        δ₂)).hom.app P ≫ k)
  rw [Functor.comp_map] at nat
  rw [Category.assoc, ← nat, ← Category.assoc, ← Adjunction.homEquiv_unit,
    Adjunction.homEquiv_naturality_right]
  rw [h₂, ← Adjunction.homEquiv_unit, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [Category.assoc]

variable (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The transpose of the left composite in the lower-singleton compatibility.
Source: Stacks 0FND and 09T5 (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: the scalar transpose moves the lower map out, the lower transpose formula turns it
into the sequence transition, and the coefficient comparison transposes to the unit. -/
theorem singletonScalarLower_transpose_left {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) :
    ((systemDerivedTensorAdj S B h).comp
        ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction)).homEquiv _ _
      (A.model.T.map (singletonLowerMap S T B h P) ≫
        (singletonScalarDerivedIso S T a A m).hom.app P) =
    ((S (a.app (op m))).adjunction.comp (singletonSequenceDerivedAdjunction S T D m)).unit.app P ≫
      (singletonDerivedRestrictionEvaluation a m).inv.app _ ≫
      (singletonSequenceDerivedTransition B h).app _ := by
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((singletonSequenceDerivedAdjunction S T B m).comp A.adjunction).ofNatIsoRight
      (singletonDerivedRestrictionEvaluation a m))
    ((S (a.app (op m))).adjunction.comp (singletonSequenceDerivedAdjunction S T D m)) P
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hu
  erw [Equiv.trans_apply] at hu
  rw [singletonScalarDerivedIso, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply, Equiv.trans_apply]
  erw [A.adjunction.homEquiv_naturality_left]
  erw [singletonLowerMap_transpose]
  rw [← hu]
  simp

/-- The transpose of the right composite in the lower-singleton compatibility.
Source: Stacks 0FND, 09T5 and 06YT (blueprint: lem-pur-system-singleton-scalar-lower).
Proof: the coefficient comparison transposes to the unit, naturality of the restriction
square moves the remaining maps across, the scalar square transposes to the restriction
compositors, and the lower transpose formula gives the sequence transition. -/
theorem singletonScalarLower_transpose_right {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) :
    ((systemDerivedTensorAdj S B h).comp
        ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction)).homEquiv _ _
      ((singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P) ≫
        (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
        singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P)) =
    ((S (a.app (op m))).adjunction.comp (singletonSequenceDerivedAdjunction S T D m)).unit.app P ≫
      (singletonLevelRestriction a m).mapDerivedCategory.map
        ((singletonSequenceDerivedTransition D h).app _) ≫
      (Functor.exactDerivedRestrictionComposition _ _ _
        (systemScalarRestrictionComposition (a.app (op m)) (D.map (homOfLE h).op)
          (B.map (homOfLE h).op ≫ a.app (op n)) (a.naturality (homOfLE h).op))).hom.app _ ≫
      (Functor.exactDerivedRestrictionComposition _ _ _
        (systemScalarRestrictionComposition (B.map (homOfLE h).op) (a.app (op n))
          (B.map (homOfLE h).op ≫ a.app (op n)) rfl)).inv.app _ ≫
      (systemRestriction B h).mapDerivedCategory.map
        ((singletonDerivedRestrictionEvaluation a n).inv.app _) := by
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).ofNatIsoRight
      (singletonDerivedRestrictionEvaluation a n))
    ((S (a.app (op n))).adjunction.comp (singletonSequenceDerivedAdjunction S T D n))
    ((systemDerivedTensor S B h).obj P)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hu
  have hX : ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).homEquiv _ _
      ((singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P)) =
      ((S (a.app (op n))).adjunction.comp
        (singletonSequenceDerivedAdjunction S T D n)).unit.app _ ≫
        (singletonDerivedRestrictionEvaluation a n).inv.app _ := by
    rw [singletonScalarDerivedIso, ← hu]
    simp
  have nat := (singletonDerivedRestrictionEvaluation a n).inv.naturality
    ((singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
      singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P))
  rw [Functor.comp_map, Functor.comp_map] at nat
  have hlow := singletonLowerMap_transpose S T D h ((S (a.app (op m))).model.T.obj P) _ (𝟙 _)
  rw [Category.comp_id] at hlow
  have hid : (S (a.app (op m))).adjunction.homEquiv _ _
      ((singletonSequenceDerivedAdjunction S T D m).homEquiv _ _ (𝟙 _)) =
      ((S (a.app (op m))).adjunction.comp
        (singletonSequenceDerivedAdjunction S T D m)).unit.app P := by
    rw [← Adjunction.homEquiv_id, Adjunction.comp_homEquiv]
    rfl
  rw [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction).homEquiv_naturality_right]
  erw [hX]
  rw [Category.assoc]
  erw [← nat]
  rw [← Category.assoc]
  erw [← ((S (a.app (op n))).adjunction.comp
    (singletonSequenceDerivedAdjunction S T D n)).homEquiv_unit]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [(singletonSequenceDerivedAdjunction S T D n).homEquiv_naturality_left
    ((singletonScalarSquare S a n m h).hom.app P)]
  erw [singletonScalarSquare_transpose]
  erw [hlow]
  rw [Adjunction.homEquiv_naturality_right]
  erw [hid]
  simp only [Category.assoc]
  rfl

end SheafOfModules
