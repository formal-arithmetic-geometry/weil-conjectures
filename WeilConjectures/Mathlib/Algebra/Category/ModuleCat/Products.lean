/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Quotient.Defs

/-!
# Elements of a coproduct of modules

The images of the injections of a colimit cofan in `ModuleCat R` span the cocone point, so every
element of a coproduct of modules is a finite sum of images of the injections.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type u} [Ring R] {ι : Type w} {Z : ι → ModuleCat.{v} R}

/-- The ranges of the injections of a colimit cofan in `ModuleCat R` span the cocone point. -/
lemma iSup_range_inj_eq_top_of_isColimit {c : Cofan Z} (hc : IsColimit c) :
    ⨆ i, LinearMap.range (c.inj i).hom = ⊤ := by
  let N := ⨆ i, LinearMap.range (c.inj i).hom
  have h : ofHom N.mkQ = 0 := Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by
    ext x
    simpa [N, Submodule.Quotient.mk_eq_zero] using
      Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self (c.inj i).hom x)
  rw [eq_top_iff]
  intro x _
  rw [← Submodule.Quotient.mk_eq_zero]
  exact congr($h x)

/-- Every element of the point of a colimit cofan in `ModuleCat R` is a finite sum of images of
the injections. -/
lemma exists_finset_sum_inj_eq_of_isColimit {c : Cofan Z} (hc : IsColimit c) (y : c.pt) :
    ∃ (t : Finset ι) (x : ∀ i, Z i), ∑ i ∈ t, c.inj i (x i) = y := by
  have hy : y ∈ ⨆ i, LinearMap.range (c.inj i).hom := by
    rw [iSup_range_inj_eq_top_of_isColimit hc]
    trivial
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).1 hy
  choose x hx using hf
  exact ⟨f.support, x, Finset.sum_congr rfl fun i _ ↦ hx i⟩

end ModuleCat
