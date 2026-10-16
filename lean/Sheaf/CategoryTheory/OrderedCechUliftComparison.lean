/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.Sites.CechInjective

/-!
# Categorical and ordered Čech complexes after lifting the finite index type

The product universal property identifies the categorical cochains with dependent
functions. Reindexing the tuples by `ULift` preserves every omitted-factor projection.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C] {V : C}
  [HasFiniteProducts (Over V)] {n : ℕ} (U : Fin n → Over V)
  (P : Cᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- Categorical product cochains are ordered cochains, after removing `ULift`. -/
noncomputable def uliftCochainEquiv (k : ℕ) :
    ((cechComplexFunctor fun i : ULift.{u + 1} (Fin n) ↦ U i.down).obj
      ((Over.forget V).op ⋙ P)).X k ≃+ ((cechComplex U).obj P).X k where
  toFun c y := cechCochainπ (fun i : ULift.{u + 1} (Fin n) ↦ U i.down) P k
    (fun l ↦ ULift.up (y l)) c
  invFun c := cechCochainMk (fun i : ULift.{u + 1} (Fin n) ↦ U i.down) P k
    (fun y ↦ c (fun l ↦ (y l).down))
  left_inv c := by
    apply cechCochain_ext
    intro y
    rw [cechCochainπ_mk]
  right_inv c := by
    funext y
    exact cechCochainπ_mk (fun i : ULift.{u + 1} (Fin n) ↦ U i.down) P k _ _
  map_add' c d := by
    funext y
    exact map_add _ c d

/-- The categorical Čech complex with the lifted index type is canonically isomorphic
to the ordered complex. The identification commutes with the alternating differential.
Source: the product universal property and Stacks Project, Tag 01EW, the Čech differential.
(blueprint: lem-cbc-ordered-cech-ulift-comparison). -/
noncomputable def orderedCechUliftIso :
    (cechComplexFunctor fun i : ULift.{u + 1} (Fin n) ↦ U i.down).obj
      ((Over.forget V).op ⋙ P) ≅ (cechComplex U).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (uliftCochainEquiv U P k).toAddCommGrpIso) (by
      rintro k l (rfl : k + 1 = l)
      apply AddCommGrpCat.ext
      intro c
      funext y
      change ((cechComplex U).obj P).d k (k + 1)
          (uliftCochainEquiv U P k c) y =
        uliftCochainEquiv U P (k + 1)
          (((cechComplexFunctor fun i : ULift.{u + 1} (Fin n) ↦ U i.down).obj
            ((Over.forget V).op ⋙ P)).d k (k + 1) c) y
      rw [cechComplex_d_apply]
      change _ = cechCochainπ (fun i : ULift.{u + 1} (Fin n) ↦ U i.down) P (k + 1) _ _
      rw [cechCochainπ_d]
      rfl)

end CategoryTheory.Presheaf
