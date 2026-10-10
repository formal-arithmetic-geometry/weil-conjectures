/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Multiplication by an integer on coproducts of abelian groups

## Main statements

- `AddCommGrpCat.isSeparator_ulift_int`: `ℤ` is a separator of the category of abelian groups.
- `AddCommGrpCat.mono_zsmul_id_ulift_int`: multiplication by a nonzero integer on `ℤ` is a
  monomorphism.
- `AddCommGrpCat.mono_sigmaMap`: a coproduct of monomorphisms of abelian groups, indexed by a type
  in a possibly smaller universe, is a monomorphism.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

/-- Multiplication by `r` on a coproduct is the coproduct of the multiplications by `r`. -/
lemma CategoryTheory.Limits.zsmul_id_sigma {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (f : ι → C) [HasCoproduct f] (r : ℤ) :
    r • 𝟙 (∐ f) = Limits.Sigma.map fun i ↦ r • 𝟙 (f i) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [Preadditive.comp_zsmul, Category.comp_id, Sigma.ι_map, Preadditive.zsmul_comp,
    Category.id_comp]

namespace AddCommGrpCat

/-- `ℤ` is a separator of the category of abelian groups. -/
lemma isSeparator_ulift_int : IsSeparator (AddCommGrpCat.of.{u} (ULift ℤ)) := by
  intro A B f g h; simp_all only [ObjectProperty.singleton_iff, AddCommGrpCat.ext_iff,
    AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply, forall_eq', ULift.forall]
  (intro x; specialize h (AddCommGrpCat.ofHom
  (AddMonoidHom.mk' (fun y => y • x) fun y z => by simp only [add_smul])) 1; aesop)

/-- Multiplication by a nonzero integer on `ℤ` is a monomorphism. -/
lemma mono_zsmul_id_ulift_int {r : ℤ} (hr : r ≠ 0) :
    Mono (r • 𝟙 (AddCommGrpCat.of.{u} (ULift ℤ))) := by
  rw [AddCommGrpCat.mono_iff_injective]
  intro a b h
  have h' : r * a.down = r * b.down := by simpa using congrArg ULift.down h
  exact ULift.ext _ _ (mul_left_cancel₀ hr h')

/-- A coproduct of monomorphisms of abelian groups is a monomorphism, also for an index type in
a smaller universe: reindex along `Equiv.ulift`. -/
lemma mono_sigmaMap {ι : Type v} {X Y : ι → AddCommGrpCat.{max v w}}
    (p : ∀ i, X i ⟶ Y i) [∀ i, Mono (p i)] : Mono (Limits.Sigma.map p) := by
  let e : ULift.{w} ι ≃ ι := Equiv.ulift
  have h : Limits.Sigma.map p = (Sigma.reindex e X).inv ≫
      Limits.Sigma.map (fun j ↦ p (e j)) ≫ (Sigma.reindex e Y).hom := by
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    obtain ⟨j, rfl⟩ := e.surjective i
    simp only [Sigma.ι_reindex_inv_assoc]
    rw [Sigma.ι_map, Limits.Sigma.ι_map_assoc]
    erw [Sigma.ι_reindex_hom]
  rw [h]
  infer_instance

end AddCommGrpCat
