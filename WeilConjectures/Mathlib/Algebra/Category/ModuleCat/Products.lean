/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Elements of images of coproducts in categories of modules

Let `G` be a functor to `R`-modules preserving a coproduct `c` of a family `Y`, and let
`π j : c.pt ⟶ Y j` be morphisms such that `c.inj i ≫ π j = 0` for `i ≠ j`. Every element `x` of
`G.obj c.pt` is a finite sum of elements of the images of the summands, so `G.map (π j) x = 0`
for all but finitely many `j` (`ModuleCat.exists_finset_forall_map_apply_eq_zero`).

## Main statements

- `ModuleCat.exists_finset_forall_map_apply_eq_zero`.
-/

@[expose] public section

open CategoryTheory Limits

namespace ModuleCat

variable {R : Type*} [Ring R] {C : Type*} [Category* C] [HasZeroMorphisms C] {β : Type*}
  {Y : β → C}

/-- Let `G` be a functor to `R`-modules preserving a coproduct `c` of a family `Y`, and let
`π j : c.pt ⟶ Y j` be morphisms with `c.inj i ≫ π j = 0` for `i ≠ j`. For every element `x` of
`G.obj c.pt`, `G.map (π j) x = 0` for all but finitely many `j`. -/
lemma exists_finset_forall_map_apply_eq_zero (G : C ⥤ ModuleCat R) [G.PreservesZeroMorphisms]
    {c : Cofan Y} (hc : IsColimit c) [PreservesColimit (Discrete.functor Y) G]
    (π : ∀ j, c.pt ⟶ Y j) (hπ : ∀ i j, i ≠ j → c.inj i ≫ π j = 0) (x : G.obj c.pt) :
    ∃ S : Finset β, ∀ j ∉ S, G.map (π j) x = 0 := by
  let N : Submodule R (G.obj c.pt) := ⨆ j, LinearMap.range (G.map (c.inj j)).hom
  have h : ofHom N.mkQ = 0 := (isColimitOfPreserves G hc).hom_ext fun ⟨j⟩ ↦ by
    ext y
    simpa [Cofan.inj] using (Submodule.Quotient.mk_eq_zero N).2
      (Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ y))
  have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (by simpa using congr(($h).hom x))
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  refine ⟨S, fun j hj ↦ ?_⟩
  refine (iSup₂_le fun i hi ↦ LinearMap.range_le_ker_iff.2 ?_ : _ ≤ LinearMap.ker
    (G.map (π j)).hom) hS
  rw [← hom_comp, ← G.map_comp, hπ i j (fun h ↦ hj (h ▸ hi)), G.map_zero, hom_zero]

end ModuleCat
