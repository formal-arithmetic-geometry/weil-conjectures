/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Sites.PresheafCechComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicTopology.SetCechNerveFreeResolution
import WeilConjectures.CategoryTheory.Sites.PresheafCechExtEdgeKernel

/-!
# Injectivity of the presheaf Čech descent edge map

Source: Stacks Project, Cohomology on Sites, Tag 079Z; Hypercoverings, Tag 01GC.
-/

@[expose] public section

universe u v w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Sheaf

/-- The Čech edge map in degree q is injective when its other filtration pieces vanish.
Source: Stacks Project, Cohomology on Sites, Tag 079Z, and Hypercoverings, Tag 01GC. -/
theorem presheafCech_ext_edge_injective
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]
    (F : Sheaf J AddCommGrpCat.{v}) (f : Arrow (Cᵒᵖ ⥤ Type v))
    (hf : Presheaf.IsLocallySurjective J f.hom) (q : ℕ) (hq : 0 < q)
    (hlower : ∀ (P : Cᵒᵖ ⥤ Type v) (b : ℕ), 0 < b → b < q →
      Subsingleton
        (Ext ((presheafToSheaf J AddCommGrpCat).obj (P ⋙ AddCommGrpCat.free)) F b))
    (hcech : IsZero ((presheafCechComplex f F.obj).homology q)) :
    Function.Injective (fun x :
      Ext ((presheafToSheaf J AddCommGrpCat).obj (f.right ⋙ AddCommGrpCat.free)) F q ↦
        (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
          (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp x (Nat.zero_add q)) := by
  intro x y hxy
  let g := fun z : Ext ((presheafToSheaf J AddCommGrpCat).obj
      (f.right ⋙ AddCommGrpCat.free)) F q ↦
    (Ext.mk₀ ((presheafToSheaf J AddCommGrpCat).map
      (Functor.whiskerRight f.hom AddCommGrpCat.free))).comp z (Nat.zero_add q)
  have hxy' : g x = g y := hxy
  have hz : g (x - y) = 0 := by
    dsimp [g] at hxy' ⊢
    rw [sub_eq_add_neg, Ext.comp_add, Ext.comp_neg, hxy', add_neg_cancel]
  have hk := presheafCech_ext_edge_kernel F f hf q hq hlower hcech (x - y) hz
  exact sub_eq_zero.mp hk

end CategoryTheory.Sheaf
