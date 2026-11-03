/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Data.Fin.Basic

/-!
# The canonical filtration after quotienting by the first member

Source: Stacks Project, Tag 0FI5, induction on a filtration in proposition-chern-class.
(blueprint: lem-pur-first-line-quotient-filtration).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}

/-- Composite of the transitions from the first member to the indicated member. -/
def flagFirstComposite (H : Fin (n + 2) → C)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ) :
    ∀ i : Fin (n + 1), H (0 : Fin (n + 1)).succ ⟶ H i.succ :=
  Fin.induction (𝟙 _) (fun j a ↦ a ≫ d j.succ)

omit [Abelian C] in
@[simp] theorem flagFirstComposite_zero (H : Fin (n + 2) → C)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ) :
    flagFirstComposite H d 0 = 𝟙 _ := rfl

omit [Abelian C] in
@[simp] theorem flagFirstComposite_succ (H : Fin (n + 2) → C)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ) (j : Fin n) :
    flagFirstComposite H d j.succ = flagFirstComposite H d j.castSucc ≫ d j.succ := rfl

omit [Abelian C] in
/-- The composite agrees with the specified ambient inclusions. -/
theorem flagFirstComposite_comp {F : C} (H : Fin (n + 2) → C)
    (ι : ∀ i, H i ⟶ F) (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ)
    (hc : ∀ j, d j ≫ ι j.succ = ι j.castSucc) (i : Fin (n + 1)) :
    flagFirstComposite H d i ≫ ι i.succ = ι (0 : Fin (n + 1)).succ := by
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    simpa only [flagFirstComposite_succ, Category.assoc, hc, Fin.succ_castSucc] using ih

/-- The reduced members are the literal cokernels of the first-member composites. -/
def flagFirstQuotient (H : Fin (n + 2) → C)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ) (i : Fin (n + 1)) : C :=
  cokernel (flagFirstComposite H d i)

/-- Transition induced by the original transition on these cokernels. -/
def flagFirstQuotientStep (H : Fin (n + 2) → C)
    (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ) (j : Fin n) :
    flagFirstQuotient H d j.castSucc ⟶ flagFirstQuotient H d j.succ :=
  cokernel.map _ _ (𝟙 _) (d j.succ) (by simp)

/-- Inclusion of each reduced member in the ambient first-member quotient. -/
def flagFirstQuotientInclusion {F : C} (H : Fin (n + 2) → C)
    (ι : ∀ i, H i ⟶ F) (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ)
    (hc : ∀ j, d j ≫ ι j.succ = ι j.castSucc) (i : Fin (n + 1)) :
    flagFirstQuotient H d i ⟶ cokernel (ι (0 : Fin (n + 1)).succ) :=
  cokernel.map _ _ (𝟙 _) (ι i.succ) (by simp [flagFirstComposite_comp H ι d hc])

private def quotientStepCokernelIso {L A B : C} (f : L ⟶ A) (g : A ⟶ B) :
    cokernel (cokernel.map f (f ≫ g) (𝟙 L) g (by simp)) ≅ cokernel g := by
  let k := cokernel.map f (f ≫ g) (𝟙 L) g (by simp)
  let q := cokernel.desc (f ≫ g) (cokernel.π g) (by simp)
  have hq : k ≫ q = 0 := by
    apply (cancel_epi (cokernel.π f)).mp
    simp [k, q, cokernel.map, Category.assoc]
  let a := cokernel.desc k q hq
  have hz : g ≫ cokernel.π (f ≫ g) ≫ cokernel.π k = 0 := by
    have hk : cokernel.π f ≫ k = g ≫ cokernel.π (f ≫ g) := cokernel.π_desc _ _ _
    calc
      _ = cokernel.π f ≫ k ≫ cokernel.π k := by rw [← Category.assoc, ← hk, Category.assoc]
      _ = 0 := by rw [cokernel.condition, comp_zero]
  let b := cokernel.desc g (cokernel.π (f ≫ g) ≫ cokernel.π k) hz
  refine ⟨a, b, ?_, ?_⟩
  · apply (cancel_epi (cokernel.π k)).mp
    apply (cancel_epi (cokernel.π (f ≫ g))).mp
    simp [a, b, q, k]
  · apply (cancel_epi (cokernel.π g)).mp
    simp [a, b, q, k]

/-- Quotienting the first member preserves the remaining successive quotients. -/
theorem flagFirstQuotient_properties {F : C} (H : Fin (n + 2) → C)
    (ι : ∀ i, H i ⟶ F) (d : ∀ j : Fin (n + 1), H j.castSucc ⟶ H j.succ)
    (hm : ∀ i, Mono (ι i)) (hc : ∀ j, d j ≫ ι j.succ = ι j.castSucc)
    (hf : IsIso (ι (Fin.last (n + 1)))) :
    (∀ i, Mono (flagFirstQuotientInclusion H ι d hc i)) ∧
    (∀ j : Fin n, flagFirstQuotientStep H d j ≫
      flagFirstQuotientInclusion H ι d hc j.succ =
        flagFirstQuotientInclusion H ι d hc j.castSucc) ∧
    IsZero (flagFirstQuotient H d 0) ∧
    IsIso (flagFirstQuotientInclusion H ι d hc (Fin.last n)) ∧
    (∀ j : Fin n, Nonempty (cokernel (flagFirstQuotientStep H d j) ≅
      cokernel (d j.succ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := hm i.succ
    dsimp only [flagFirstQuotientInclusion]
    exact Abelian.mono_cokernel_map_of_isPullback
      (IsPullback.of_vert_isIso_mono (snd := 𝟙 _)
        ⟨by simp [flagFirstComposite_comp H ι d hc]⟩)
  · intro j
    apply (cancel_epi (cokernel.π (flagFirstComposite H d j.castSucc))).mp
    simp [flagFirstQuotientStep, flagFirstQuotientInclusion, cokernel.map,
      Category.assoc, reassoc_of% hc j.succ, -Fin.castSucc_succ]
    rfl
  · have : Epi (flagFirstComposite H d 0) := by
      change Epi (𝟙 _)
      infer_instance
    exact isZero_cokernel_of_epi (flagFirstComposite H d 0)
  · dsimp [flagFirstQuotientInclusion]
    infer_instance
  · intro j
    exact ⟨quotientStepCokernelIso (flagFirstComposite H d j.castSucc) (d j.succ)⟩

end CategoryTheory
