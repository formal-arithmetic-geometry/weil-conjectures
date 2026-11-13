/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # The explicit quotient of affine residue cycles by residue boundaries

## References

* Stacks Project, Tag 010V
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

noncomputable section

variable (W : Scheme.{v}) (U : W.Opens) (p : Ideal Γ(W, U)) [p.IsPrime]

/-- Evaluation at the top of the localized site, followed by residue extension.
-/
abbrev affineResidueTerm
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (j : ℤ) :=
  p.ResidueField ⊗[Γ(W, U)] (K.X j).val.obj (.op (Over.mk (𝟙 U)))

/-- The actual residue differential; no model or witness is chosen.
-/
abbrev affineResidueDifferential
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) (i j : ℤ) :
    affineResidueTerm W U p K i →ₗ[p.ResidueField] affineResidueTerm W U p K j :=
  (show (K.X i).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
    (K.X j).val.obj (.op (Over.mk (𝟙 U))) from
      ((K.d i j).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField

/-- Degree-one residue cycles.
-/
abbrev affineResidueCycles
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
  LinearMap.ker (affineResidueDifferential W U p K 1 2)

/-- Incoming residue boundaries, viewed as an additive subgroup of cycles.
-/
def affineResidueBoundaries
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    AddSubgroup (affineResidueCycles W U p K) :=
  (affineResidueDifferential W U p K 0 1).range.toAddSubgroup.comap
    (affineResidueCycles W U p K).subtype.toAddMonoidHom

/-- The concrete degree-one homology quotient.
-/
abbrev affineResidueCycleHomology
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :=
  affineResidueCycles W U p K ⧸ affineResidueBoundaries W U p K

/-- The canonical cycle-class map.
-/
def affineResidueCycleClass
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    affineResidueCycles W U p K →+ affineResidueCycleHomology W U p K :=
  QuotientAddGroup.mk' (affineResidueBoundaries W U p K)

/-- The residue cycle-class map is onto and its kernel is precisely incoming boundaries
(Stacks, Tag 010V). -/
theorem affineResidueCycleClass_surjective_kernel
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ) :
    Function.Surjective (affineResidueCycleClass W U p K) ∧
      ∀ x : affineResidueCycles W U p K,
        affineResidueCycleClass W U p K x = 0 ↔
          ∃ y, affineResidueDifferential W U p K 0 1 y = x.val := by
  refine ⟨QuotientAddGroup.mk'_surjective _, ?_⟩
  intro x
  exact QuotientAddGroup.eq_zero_iff x

variable {W U p}

/-- A chain map evaluated and extended to the residue field.
-/
abbrev affineResidueComponent
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (j : ℤ) :
    affineResidueTerm W U p K j →ₗ[p.ResidueField] affineResidueTerm W U p C j :=
  (show (K.X j).val.obj (.op (Over.mk (𝟙 U))) →ₗ[Γ(W, U)]
    (C.X j).val.obj (.op (Over.mk (𝟙 U))) from
      ((φ.f j).val.app (.op (Over.mk (𝟙 U)))).hom).baseChange p.ResidueField

/-- Evaluation and scalar extension preserve the chain-map commutation equations.
-/
theorem affineResidueComponent_comm
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (i j : ℤ) :
    (affineResidueDifferential W U p C i j).comp (affineResidueComponent φ i) =
      (affineResidueComponent φ j).comp (affineResidueDifferential W U p K i j) := by
  let F := SheafOfModules.evaluation
    ((moduleRings W.toRingedSpace).over U) (.op (Over.mk (𝟙 U)))
  have h := congrArg (fun g ↦ (F.map g).hom) (φ.comm i j)
  simp only [Functor.map_comp, ModuleCat.hom_comp] at h
  exact (LinearMap.baseChange_comp _ _).symm.trans
    ((congrArg (LinearMap.baseChange p.ResidueField) h).trans
      (LinearMap.baseChange_comp _ _))

/-- The degree-one cycle map of a chain map.
-/
def affineResidueCycleMap
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) : affineResidueCycles W U p K →+ affineResidueCycles W U p C where
  toFun x := ⟨affineResidueComponent φ 1 x.val, by
    change affineResidueDifferential W U p C 1 2 (affineResidueComponent φ 1 x.val) = 0
    rw [← LinearMap.comp_apply, affineResidueComponent_comm, LinearMap.comp_apply]
    rw [x.property, map_zero]⟩
  map_zero' := by ext; exact map_zero _
  map_add' x y := by ext; exact map_add _ _ _

/-- The homology map induced by a chain map on the explicit residue quotient.
-/
def affineResidueCycleHomologyMap
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) : affineResidueCycleHomology W U p K →+
      affineResidueCycleHomology W U p C :=
  QuotientAddGroup.lift (affineResidueBoundaries W U p K)
    ((affineResidueCycleClass W U p C).comp (affineResidueCycleMap φ)) (by
      intro x hx
      apply (affineResidueCycleClass_surjective_kernel W U p C).2 _ |>.mpr
      obtain ⟨y, hy⟩ := hx
      refine ⟨affineResidueComponent φ 0 y, ?_⟩
      change affineResidueDifferential W U p C 0 1 (affineResidueComponent φ 0 y) =
        affineResidueComponent φ 1 x.val
      rw [← LinearMap.comp_apply, affineResidueComponent_comm, LinearMap.comp_apply, hy]
      rfl)

/-- Chain maps commute with the cycle-class projections (Stacks, Tag 010V). -/
theorem affineResidueCycleHomologyMap_class
    {K C : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ}
    (φ : K ⟶ C) (x : affineResidueCycles W U p K) :
    affineResidueCycleHomologyMap φ (affineResidueCycleClass W U p K x) =
      affineResidueCycleClass W U p C (affineResidueCycleMap φ x) := rfl

end

end AlgebraicGeometry.Scheme
