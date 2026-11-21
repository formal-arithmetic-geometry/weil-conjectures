/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! A solution set for the universe-enlarged Hom functor. -/

@[expose] public section

universe w u vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- A well-powered abelian category with sufficiently large coproducts gives
a small solution set for the lifted Hom functor of any object.

Source: Stacks Project Lemma 19.14.1 (Tag 0F5S). -/
theorem large_hom_solutionSetCondition
    {C : Type u} [Category.{w} C] [Abelian C] [WellPowered.{w} C]
    [HasCoproducts.{max w vH} C] (G : C) :
    SolutionSetCondition.{w} (preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} (End G)ᵐᵒᵖ) := by
  -- Use the generators-and-relations construction of the second proof of
  -- Stacks Tag 0F5S, rather than the image argument described above.
  -- The relation coproduct imposes additivity and End(G)^op-linearity.
  -- Its cokernel supplies one object through which every module map factors,
  -- so the solution family is indexed by PUnit in Type w.
  classical
  intro A
  let P : C := ∐ fun _ : A => G
  let i : A → (G ⟶ P) := Sigma.ι (fun _ : A => G)
  let R := (End G)ᵐᵒᵖ
  let J := (A × A) ⊕ (R × A)
  let rel : J → (G ⟶ P) := fun j =>
    match j with
    | .inl (a, b) => i (a + b) - i a - i b
    | .inr (r, a) => i (r • a) - (r.unop).asHom ≫ i a
  let d : (∐ fun _ : J => G) ⟶ P := Sigma.desc rel
  let Q := cokernel d
  let q : P ⟶ Q := cokernel.π d
  have hrel (j : J) : rel j ≫ q = 0 := by
    rw [← Sigma.ι_comp_desc rel j, Category.assoc, cokernel.condition, comp_zero]
  have hadd (a b : A) : i (a + b) ≫ q = i a ≫ q + i b ≫ q := by
    have h := hrel (.inl (a, b))
    change (i (a + b) - i a - i b) ≫ q = 0 at h
    simpa only [Preadditive.sub_comp, sub_sub, sub_eq_zero, Preadditive.add_comp] using h
  have hsmul (r : R) (a : A) : i (r • a) ≫ q = (r.unop).asHom ≫ (i a ≫ q) := by
    have h := hrel (.inr (r, a))
    change (i (r • a) - r.unop.asHom ≫ i a) ≫ q = 0 at h
    simpa only [Preadditive.sub_comp, Category.assoc, sub_eq_zero] using h
  let f : A ⟶ (preadditiveCoyonedaObj G ⋙
      ModuleCat.uliftFunctor.{vH, w} (End G)ᵐᵒᵖ).obj Q := ModuleCat.ofHom
    { toFun := fun a => ULift.up (i a ≫ q)
      map_add' := fun a b => congrArg ULift.up (hadd a b)
      map_smul' := fun r a => congrArg ULift.up (hsmul r a) }
  refine ⟨PUnit, fun _ => Q, fun _ => f, ?_⟩
  intro X h
  let k : P ⟶ X := Sigma.desc (fun a => (h a).down)
  have hik (a : A) : i a ≫ k = (h a).down := Sigma.ι_comp_desc _ a
  have hd : d ≫ k = 0 := by
    apply Sigma.hom_ext
    intro j
    change Sigma.ι (fun _ : J => G) j ≫ Sigma.desc rel ≫ k = _
    rw [Sigma.ι_comp_desc_assoc, comp_zero]
    cases j with
    | inl ab =>
      rcases ab with ⟨a, b⟩
      change (i (a + b) - i a - i b) ≫ k = 0
      rw [Preadditive.sub_comp, Preadditive.sub_comp, hik, hik, hik]
      have hh := congrArg ULift.down (h.hom.map_add a b)
      change (h (a + b)).down = (h a).down + (h b).down at hh
      rw [hh, add_sub_cancel_left, sub_self]
    | inr ra =>
      rcases ra with ⟨r, a⟩
      change (i (r • a) - r.unop.asHom ≫ i a) ≫ k = 0
      rw [Preadditive.sub_comp, Category.assoc, hik, hik]
      have hh := congrArg ULift.down (h.hom.map_smul r a)
      change (h (r • a)).down = r.unop.asHom ≫ (h a).down at hh
      rw [hh, sub_self]
  refine ⟨PUnit.unit, cokernel.desc d k hd, ?_⟩
  ext a
  change ULift.up ((i a ≫ q) ≫ cokernel.desc d k hd) = h a
  rw [Category.assoc, cokernel.π_desc, hik]
  exact ULift.up_down (h a)

end CategoryTheory
