/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf

/-!
# The submodule of locally liftable sections

Given a morphism `φ : M ⟶ N` of presheaves of modules over a category `C` equipped with a
Grothendieck topology `J`, the sections of `N` over `U` which lift along `φ` on a covering
sieve of `U` form a submodule `PresheafOfModules.localImage J φ U` of `N.obj U`. Local
surjectivity of `φ` is the statement that this submodule is everything, so checking local
surjectivity may be done on a generating family of sections.
-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {M N : PresheafOfModules.{u} R₀} (φ : M ⟶ N)

/-- The sections of `N` over `U` which lift along `φ` on a covering sieve of `U`. -/
def localImage (U : Cᵒᵖ) : Submodule (R₀.obj U) (N.obj U) where
  carrier := {s | Presheaf.imageSieve ((toPresheaf R₀).map φ) s ∈ J U.unop}
  zero_mem' := by
    refine J.superset_covering (fun V g _ ↦ ⟨0, ?_⟩) (J.top_mem _)
    change φ.app (op V) 0 = N.map g.op 0
    rw [map_zero, map_zero]
  add_mem' {s₁ s₂} h₁ h₂ := by
    refine J.superset_covering (fun V g hg ↦ ?_) (J.intersection_covering h₁ h₂)
    obtain ⟨⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ :
      (∃ t : M.obj (op V), φ.app (op V) t = N.map g.op s₁) ∧
        ∃ t : M.obj (op V), φ.app (op V) t = N.map g.op s₂ := hg
    refine ⟨t₁ + t₂, ?_⟩
    change φ.app (op V) (t₁ + t₂) = N.map g.op (s₁ + s₂)
    rw [map_add, map_add, ht₁, ht₂]
  smul_mem' r s h := by
    refine J.superset_covering (fun V g hg ↦ ?_) h
    obtain ⟨t, ht⟩ : ∃ t : M.obj (op V), φ.app (op V) t = N.map g.op s := hg
    refine ⟨R₀.map g.op r • t, ?_⟩
    change φ.app (op V) (R₀.map g.op r • t) = N.map g.op (r • s)
    rw [N.map_smul, ← ht]
    exact (φ.app (op V)).hom.map_smul _ _

lemma mem_localImage {U : Cᵒᵖ} (s : N.obj U) :
    s ∈ localImage J φ U ↔ Presheaf.imageSieve ((toPresheaf R₀).map φ) s ∈ J U.unop :=
  Iff.rfl

end PresheafOfModules
