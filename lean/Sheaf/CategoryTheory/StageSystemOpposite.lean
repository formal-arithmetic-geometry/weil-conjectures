/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Opposites

/-! # Opposite stages and contravariant common-stage descent

The opposite of a stage system uses the inverse opposite associator. Reversing
finite-stage representatives identifies its pair category with the opposite of
the original pair category. This implements the representative construction in
blueprint `thm-coef-qbar-verdier`, proof steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u v
open Opposite

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- Opposite stages, with the inverse opposite associator. -/
def opposite (S : StageSystem C) : StageSystem (fun i ↦ (C i)ᵒᵖ) where
  T h := (S.T h).op
  assoc h k := NatIso.op (S.assoc h k).symm
  cocycle h k m X := by
    apply Quiver.Hom.unop_inj
    exact S.cocycle_inv h k m X.unop

variable (S : StageSystem C)

/-- Reversing a representative commutes with further transport. -/
theorem opposite_transport {i j n p : I} {hi : i ≤ n} {hj : j ≤ n}
    (h : n ≤ p) {X : C i} {Y : C j}
    (f : (S.T hi).obj X ⟶ (S.T hj).obj Y) :
    (S.opposite.tr (hi := hj) (hj := hi) h f.op).unop = S.tr h f := by
  simp [tr, opposite, Category.assoc]

variable [IsDirectedOrder I]

/-- The original pair underlying an object of the opposite-stage pair category. -/
abbrev unopPair (P : S.opposite.PairCategory) : S.PairCategory := ⟨P.stage, P.obj.unop⟩

/-- Reverse each representative into the opposite pair category. -/
def pairOppositeFunctor : S.opposite.PairCategory ⥤ S.PairCategoryᵒᵖ where
  obj P := op (S.unopPair P)
  map {P Q} f := Quiver.Hom.op (show S.unopPair Q ⟶ S.unopPair P from Quotient.map
    (sa := PairCategory.Rep.setoid P Q)
    (sb := PairCategory.Rep.setoid (S.unopPair Q) (S.unopPair P))
    (fun r ↦ ⟨r.k, r.hY, r.hX, r.u.unop⟩)
    (by
      rintro r s ⟨n, hr, hs, e⟩
      refine ⟨n, hr, hs, ?_⟩
      simpa [tr, opposite, Category.assoc] using congrArg Quiver.Hom.unop e) f)
  map_id P := by
    apply Quiver.Hom.unop_inj
    change _ = 𝟙 (S.unopPair P)
    rw [PairCategory.id_eq_mkHom P le_rfl,
      PairCategory.id_eq_mkHom (S.unopPair P) le_rfl]
    rfl
  map_comp {P Q R} f g := by
    apply Quiver.Hom.unop_inj
    obtain ⟨n, -, hP, hQ, hQ', hR, a, b, rfl, rfl⟩ :=
      PairCategory.exists_common_stage f g P.stage
    rw [PairCategory.mkHom_comp_mkHom]
    change PairCategory.mkHom (X := S.unopPair R) (Y := S.unopPair P) n hR hP
        (a ≫ b).unop =
      PairCategory.mkHom (X := S.unopPair R) (Y := S.unopPair Q) n hR hQ' b.unop ≫
        PairCategory.mkHom (X := S.unopPair Q) (Y := S.unopPair P) n hQ hP a.unop
    rw [PairCategory.mkHom_comp_mkHom]
    rfl


/-- Reverse a pair into the opposite-stage system. -/
abbrev opPair (P : S.PairCategory) : S.opposite.PairCategory := ⟨P.stage, op P.obj⟩

/-- Reverse an ordinary pair arrow into the opposite-stage system. -/
def opPairHom {P Q : S.PairCategory} (f : P ⟶ Q) : S.opPair Q ⟶ S.opPair P :=
  Quotient.map
    (sa := PairCategory.Rep.setoid P Q)
    (sb := PairCategory.Rep.setoid (S.opPair Q) (S.opPair P))
    (fun r ↦ ⟨r.k, r.hY, r.hX, r.u.op⟩)
    (by
      rintro r s ⟨n, hr, hs, e⟩
      refine ⟨n, hr, hs, ?_⟩
      apply Quiver.Hom.unop_inj
      simpa [tr, opposite, Category.assoc] using e) f

/-- The inverse functor sends an opposite arrow to its opposite representative. -/
def pairUnopFunctor : S.PairCategoryᵒᵖ ⥤ S.opposite.PairCategory where
  obj P := S.opPair P.unop
  map f := S.opPairHom f.unop
  map_id P := by
    change S.opPairHom (𝟙 P.unop) = 𝟙 (S.opPair P.unop)
    rw [PairCategory.id_eq_mkHom P.unop le_rfl,
      PairCategory.id_eq_mkHom (S.opPair P.unop) le_rfl]
    rfl
  map_comp {P Q R} f g := by
    change S.opPairHom (g.unop ≫ f.unop) =
      S.opPairHom f.unop ≫ S.opPairHom g.unop
    obtain ⟨n, -, hR, hQ, hQ', hP, a, b, ha, hb⟩ :=
      PairCategory.exists_common_stage g.unop f.unop R.unop.stage
    rw [ha, hb, PairCategory.mkHom_comp_mkHom]
    change PairCategory.mkHom (X := S.opPair P.unop) (Y := S.opPair R.unop) n hP hR
        (a ≫ b).op =
      PairCategory.mkHom (X := S.opPair P.unop) (Y := S.opPair Q.unop) n hP hQ' b.op ≫
        PairCategory.mkHom (X := S.opPair Q.unop) (Y := S.opPair R.unop) n hQ hR a.op
    rw [PairCategory.mkHom_comp_mkHom]
    rfl

/-- Reversing representatives twice fixes every pair and every arrow. -/
def pairOppositeUnit : 𝟭 S.opposite.PairCategory ≅
    S.pairOppositeFunctor ⋙ S.pairUnopFunctor :=
  NatIso.ofComponents (fun P ↦ Iso.refl P) (fun {P Q} f ↦ by
    induction f using PairCategory.hom_induction with
    | h n hP hQ a =>
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      simp only [Category.comp_id, Category.id_comp]
      rfl)

/-- The second composite also fixes pairs and arrows. -/
def pairOppositeCounit : S.pairUnopFunctor ⋙ S.pairOppositeFunctor ≅
    𝟭 S.PairCategoryᵒᵖ :=
  NatIso.ofComponents (fun P ↦ Iso.refl P) (fun {P Q} f ↦ by
    apply Quiver.Hom.unop_inj
    simp only [unop_comp]
    change 𝟙 Q.unop ≫ (S.pairOppositeFunctor.map (S.opPairHom f.unop)).unop =
      f.unop ≫ 𝟙 P.unop
    simp only [Category.id_comp, Category.comp_id]
    generalize f.unop = a
    induction a using PairCategory.hom_induction with
    | h n hP hQ a => rfl)


/-- Opposite finite stages present the opposite common-stage category.
Source: blueprint thm-coef-qbar-verdier, opposite-category representative construction
(blueprint: lem-coef-qbar-opposite-stage-pairs).

Proof: the opposite associator is the opposite of the inverse associator. Its
cocycle is the inverse cocycle. Reversing a representative reverses its source and
target bounds and its arrow; the transport formula is preserved because the two
inverse associators are also reversed. Thus eventual equality is preserved in both
directions. Finite-stage functoriality gives the two functor laws, and reversing
representatives twice is the identity on both objects and quotient classes. -/
def pairOppositeEquivalence : S.opposite.PairCategory ≌ S.PairCategoryᵒᵖ where
  functor := S.pairOppositeFunctor
  inverse := S.pairUnopFunctor
  unitIso := S.pairOppositeUnit
  counitIso := S.pairOppositeCounit
  functor_unitIso_comp X := by
    change S.pairOppositeFunctor.map (𝟙 X) ≫ 𝟙 _ = 𝟙 _
    simp

end CategoryTheory.StageSystem
