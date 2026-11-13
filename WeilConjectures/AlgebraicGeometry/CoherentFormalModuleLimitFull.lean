/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleLimitQuotient

/-! # Reconstructing formal-system maps from maps of limit sheaves

Source: Stacks Project, Lemma 087W, and the uniqueness/gluing step of Lemma 088B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every module-sheaf map between the limits of coherent adic systems descends
uniquely at each level to a compatible map of systems; here only existence is asserted.
Source: Stacks Project, Lemma 087W, its formula M/I^n M = M_n, and Lemma 088B,
the construction of alpha through that equivalence and local uniqueness. -/
theorem coherentFormalModule_limit_full {Y : Scheme.{u}} [IsNoetherian Y]
    (J : Y.IdealSheafData) (G H : CoherentFormalModule Y J)
    (β : limit G.obj ⟶ limit H.obj) :
    ∃ α : G ⟶ H, lim.map α.hom = β := by
  classical
  have hG := coherentFormalModule_limit_quotient J G
  have hH := coherentFormalModule_limit_quotient J H
  let eG (n : ℕ) := (hG n).choose
  let eH (n : ℕ) := (hH n).choose
  have heG (n : ℕ) : formalModuleQuotientπ J (n + 1) (limit G.obj) ≫
      (eG n).hom = limit.π G.obj (op n) := (hG n).choose_spec
  have heH (n : ℕ) : formalModuleQuotientπ J (n + 1) (limit H.obj) ≫
      (eH n).hom = limit.π H.obj (op n) := (hH n).choose_spec
  let a (n : ℕ) : G.obj.obj (op n) ⟶ H.obj.obj (op n) :=
    (eG n).inv ≫ formalModuleQuotientMap J β (Nat.le_refl (n + 1)) ≫ (eH n).hom
  have ha (n : ℕ) : limit.π G.obj (op n) ≫ a n = β ≫ limit.π H.obj (op n) := by
    rw [← heG, ← heH]
    simp [a, formalModuleQuotientMap, formalModuleQuotientπ, Category.assoc]
  have hπ (n : ℕ) : Epi (limit.π G.obj (op n)) := by
    rw [← heG]
    dsimp [formalModuleQuotientπ]
    infer_instance
  let t : G.obj ⟶ H.obj :=
    { app := fun n ↦ a n.unop
      naturality := by
        intro i j f
        have := hπ i.unop
        apply (cancel_epi (limit.π G.obj i)).1
        change limit.π G.obj i ≫ (G.obj.map f ≫ a j.unop) =
          limit.π G.obj i ≫ (a i.unop ≫ H.obj.map f)
        rw [← Category.assoc, limit.w, ha j.unop, ← Category.assoc, ha i.unop]
        simp only [Category.assoc, limit.w] }
  refine ⟨ObjectProperty.homMk t, ?_⟩
  apply limit.hom_ext
  intro n
  exact (limMap_π t n).trans (ha n.unop)

end AlgebraicGeometry
