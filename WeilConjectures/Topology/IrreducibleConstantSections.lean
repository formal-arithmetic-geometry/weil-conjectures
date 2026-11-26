/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.Topology.ConstantSheafLocallyConstantComparison

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u v

namespace TopCat

/-! # Sections of a constant sheaf on an irreducible space

On an irreducible space, sections of the constant sheaf over nonempty opens are the coefficient
group.

## Implementation details

The constant sheaf is identified with the sheaf of locally constant maps. Every nonempty open of
an irreducible space is irreducible, hence connected, so locally constant maps on it are
constant.

## References

* [Stacks Project, Tags 006W and 0081](https://stacks.math.columbia.edu/tag/006W)
-/

/-- Sections of the constant sheaf on nonempty opens of an irreducible space are canonically
identified with the coefficient group, compatibly with restriction. -/
theorem irreducible_constant_sections
    (X : TopCat.{u}) [IrreducibleSpace X]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    (A : Type v) [AddCommGroup A] :
    ∃ e : ∀ U : Opens X, (U : Set X).Nonempty →
      AddEquiv (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of A)).1.obj (op U)) A,
      ∀ (U V : Opens X) (hVU : V ≤ U) (hV : (V : Set X).Nonempty),
        e V hV ∘ ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of A)).1.map (homOfLE hVU).op = e U (Set.Nonempty.mono hVU hV) := by
  classical
  obtain ⟨c, hc⟩ := constantSheaf_locallyConstant_comparison X A
  let point (U : Opens X) (hU : (U : Set X).Nonempty) : U := ⟨hU.choose, hU.choose_spec⟩
  have preconnected (U : Opens X) : PreconnectedSpace U := by
    let : PreirreducibleSpace U := U.isOpenEmbedding'.preirreducibleSpace
    infer_instance
  let eval (U : Opens X) (hU : (U : Set X).Nonempty) : LocallyConstant U A ≃+ A :=
    { toFun := fun f ↦ f (point U hU)
      invFun := LocallyConstant.const U
      left_inv := by
        intro f
        let := preconnected U
        exact (f.eq_const (point U hU)).symm
      right_inv := by intro a; rfl
      map_add' := by intro f g; rfl }
  refine ⟨fun U hU ↦ (c U).trans (eval U hU), ?_⟩
  intro U V hVU hV
  funext s
  change c V (((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
    (AddCommGrpCat.of A)).1.map (homOfLE hVU).op s) (point V hV) =
      c U s (point U (Set.Nonempty.mono hVU hV))
  rw [hc]
  let := preconnected U
  exact (c U s).apply_eq_of_preconnectedSpace _ _

end TopCat
