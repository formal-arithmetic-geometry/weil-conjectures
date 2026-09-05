/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.QlbarCoefficient.CommonStage.Defs

/-!
# The additive structure on the common-stage category

If all the categories `C i` of a `CategoryTheory.TransitionSystem` are preadditive and all
the transition functors are additive, then the common-stage category is preadditive: sums
of morphisms are computed after transport to a common stage.

## Main definitions

- `CategoryTheory.TransitionSystem.IsAdditive`: the property that all transition functors
  are additive.
- `CategoryTheory.TransitionSystem.CommonStage.homAddCommGroup`: the abelian group
  structure on the `Hom` types.
- `CategoryTheory.TransitionSystem.CommonStage.preadditive`: the `Preadditive` instance.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category

variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  [∀ i, Preadditive (C i)]

/-- A transition system between preadditive categories is additive if all of its transition
functors are additive. -/
class TransitionSystem.IsAdditive (S : TransitionSystem C) : Prop where
  /-- The transition functors are additive. -/
  additive {i j : I} (h : i ≤ j) : (S.T h).Additive

attribute [instance] TransitionSystem.IsAdditive.additive

namespace TransitionSystem.CommonStage

variable {S : TransitionSystem C} [S.IsAdditive] {X Y Z : CommonStage S} {k l : I}

section Transport

variable {hX : X.stage ≤ k} {hY : Y.stage ≤ k}

@[simp]
lemma transport_add (hkl : k ≤ l) (u v : X.extend hX ⟶ Y.extend hY) :
    transport hkl (u + v) = transport hkl u + transport hkl v := by
  simp [transport, Preadditive.comp_add, Preadditive.add_comp]

@[simp]
lemma transport_zero (hkl : k ≤ l) :
    transport (hX := hX) (hY := hY) hkl 0 = 0 := by
  simp [transport]

@[simp]
lemma transport_neg (hkl : k ≤ l) (u : X.extend hX ⟶ Y.extend hY) :
    transport hkl (-u) = -transport hkl u := by
  simp [transport, Preadditive.comp_neg, Preadditive.neg_comp]

end Transport

variable [IsDirectedOrder I]

/-- Addition of morphisms, as a stagewise binary operation. -/
noncomputable def addBinop (X Y : CommonStage S) : StageBinop X Y where
  op _ _ u v := u + v
  transport_op _ _ hkl u v := transport_add hkl u v

/-- Negation of morphisms, as a stagewise unary operation. -/
noncomputable def negUnop (X Y : CommonStage S) : StageUnop X Y where
  op _ _ u := -u
  transport_op _ _ hkl u := transport_neg hkl u

/-- The zero morphism, represented at a common stage for the two objects. -/
noncomputable def zeroHom (X Y : CommonStage S) : X ⟶ Y :=
  homMk (le_ub_left X.stage Y.stage) (le_ub_right X.stage Y.stage) 0

noncomputable instance homAddCommGroup (X Y : CommonStage S) : AddCommGroup (X ⟶ Y) :=
  letI : Add (X ⟶ Y) := ⟨(addBinop X Y).lift⟩
  letI : Zero (X ⟶ Y) := ⟨zeroHom X Y⟩
  letI : Neg (X ⟶ Y) := ⟨(negUnop X Y).lift⟩
  { add := (· + ·)
    zero := 0
    neg := (- ·)
    nsmul := nsmulRec
    zsmul := zsmulRec
    add_assoc := fun f g h ↦ by
      obtain ⟨k, hX, hY, u, v, w, rfl, rfl, rfl⟩ := exists_homMk₃ f g h
      change (addBinop X Y).lift ((addBinop X Y).lift _ _) _ =
        (addBinop X Y).lift _ ((addBinop X Y).lift _ _)
      simp only [StageBinop.lift_homMk]
      exact congrArg (homMk hX hY) (add_assoc u v w)
    add_comm := fun f g ↦ by
      obtain ⟨k, hX, hY, u, v, rfl, rfl⟩ := exists_homMk₂ f g
      change (addBinop X Y).lift _ _ = (addBinop X Y).lift _ _
      simp only [StageBinop.lift_homMk]
      exact congrArg (homMk hX hY) (add_comm u v)
    zero_add := fun f ↦ by
      obtain ⟨k, hX, hY, u, rfl⟩ := exists_homMk f
      obtain ⟨p, h₁, h₂⟩ := exists_ge_ge (ub I X.stage Y.stage) k
      change (addBinop X Y).lift (zeroHom X Y) _ = _
      rw [zeroHom, ← homMk_transport (le_ub_left X.stage Y.stage)
          (le_ub_right X.stage Y.stage) h₁ 0,
        ← homMk_transport hX hY h₂ u, transport_zero, StageBinop.lift_homMk]
      exact congrArg (homMk _ _) (zero_add _)
    add_zero := fun f ↦ by
      obtain ⟨k, hX, hY, u, rfl⟩ := exists_homMk f
      obtain ⟨p, h₁, h₂⟩ := exists_ge_ge (ub I X.stage Y.stage) k
      change (addBinop X Y).lift _ (zeroHom X Y) = _
      rw [zeroHom, ← homMk_transport (le_ub_left X.stage Y.stage)
          (le_ub_right X.stage Y.stage) h₁ 0,
        ← homMk_transport hX hY h₂ u, transport_zero, StageBinop.lift_homMk]
      exact congrArg (homMk _ _) (add_zero _)
    neg_add_cancel := fun f ↦ by
      obtain ⟨k, hX, hY, u, rfl⟩ := exists_homMk f
      obtain ⟨p, h₁, h₂⟩ := exists_ge_ge (ub I X.stage Y.stage) k
      change (addBinop X Y).lift ((negUnop X Y).lift _) _ = zeroHom X Y
      rw [zeroHom, ← homMk_transport (le_ub_left X.stage Y.stage)
          (le_ub_right X.stage Y.stage) h₁ 0,
        ← homMk_transport hX hY h₂ u, transport_zero, StageUnop.lift_homMk,
        StageBinop.lift_homMk]
      exact congrArg (homMk _ _) (neg_add_cancel _) }

@[simp]
lemma homMk_add (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u v : X.extend hX ⟶ Y.extend hY) :
    homMk hX hY u + homMk hX hY v = homMk hX hY (u + v) :=
  (addBinop X Y).lift_homMk hX hY u v

@[simp]
lemma homMk_neg (hX : X.stage ≤ k) (hY : Y.stage ≤ k) (u : X.extend hX ⟶ Y.extend hY) :
    -homMk hX hY u = homMk hX hY (-u) :=
  (negUnop X Y).lift_homMk hX hY u

@[simp]
lemma homMk_zero (hX : X.stage ≤ k) (hY : Y.stage ≤ k) :
    homMk hX hY (0 : X.extend hX ⟶ Y.extend hY) = 0 := by
  obtain ⟨p, h₁, h₂⟩ := exists_ge_ge k (ub I X.stage Y.stage)
  change _ = zeroHom X Y
  rw [zeroHom, ← homMk_transport hX hY h₁ (0 : X.extend hX ⟶ Y.extend hY),
    ← homMk_transport (le_ub_left X.stage Y.stage) (le_ub_right X.stage Y.stage) h₂
      (0 : X.extend _ ⟶ Y.extend _), transport_zero, transport_zero]

noncomputable instance preadditive : Preadditive (CommonStage S) where
  homGroup := homAddCommGroup
  add_comp P Q R f f' g := by
    obtain ⟨k₁, hX, hY, u, u', rfl, rfl⟩ := exists_homMk₂ f f'
    obtain ⟨k₂, hY', hZ, v, rfl⟩ := exists_homMk g
    obtain ⟨k, h₁, h₂⟩ := exists_ge_ge k₁ k₂
    rw [← homMk_transport hX hY h₁ u, ← homMk_transport hX hY h₁ u',
      ← homMk_transport hY' hZ h₂ v, homMk_add, homMk_comp_homMk, homMk_comp_homMk,
      homMk_comp_homMk, homMk_add, Preadditive.add_comp]
  comp_add P Q R f g g' := by
    obtain ⟨k₁, hX, hY, u, rfl⟩ := exists_homMk f
    obtain ⟨k₂, hY', hZ, v, v', rfl, rfl⟩ := exists_homMk₂ g g'
    obtain ⟨k, h₁, h₂⟩ := exists_ge_ge k₁ k₂
    rw [← homMk_transport hX hY h₁ u, ← homMk_transport hY' hZ h₂ v,
      ← homMk_transport hY' hZ h₂ v', homMk_add, homMk_comp_homMk, homMk_comp_homMk,
      homMk_comp_homMk, homMk_add, Preadditive.comp_add]

end TransitionSystem.CommonStage

end CategoryTheory
