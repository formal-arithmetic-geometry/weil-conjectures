/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts

/-! # Geometric charts for smooth exceptional base change

The global-target version of the étale normal form lets us take the final base
open immersion in the chart argument to be the identity.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The coordinates other than the zeroth homogeneous coordinate. -/
def purityChartIndexEquiv (n : ℕ) :
    ULift.{u} (Fin n) ≃ {j : ULift.{u} (Fin (n + 1)) // j ≠ ⟨0⟩} :=
  (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).trans
    ((finSuccAboveEquiv (0 : Fin (n + 1))).trans
      ((Equiv.ulift : ULift.{u} (Fin (n + 1)) ≃ Fin (n + 1)).symm.subtypeEquiv
        (fun x ↦ by simp)))

/-- The standard open embedding of affine n-space into projective n-space. -/
def purityAffineProjectiveOpen (n : ℕ) (Y : Scheme.{u}) :
    𝔸(ULift.{u} (Fin n); Y) ⟶ ℙ(ULift.{u} (Fin (n + 1)); Y) :=
  (AffineSpace.reindexIso Y (purityChartIndexEquiv n).symm).hom ≫
    (ProjectiveSpace.standardOpenIso (ULift.{u} (Fin (n + 1))) Y ⟨0⟩).inv ≫
      (ProjectiveSpace.standardOpen (ULift.{u} (Fin (n + 1))) Y ⟨0⟩).ι

instance (n : ℕ) (Y : Scheme.{u}) : IsOpenImmersion (purityAffineProjectiveOpen n Y) := by
  unfold purityAffineProjectiveOpen
  infer_instance

@[reassoc]
lemma purityAffineProjectiveOpen_over (n : ℕ) (Y : Scheme.{u}) :
    purityAffineProjectiveOpen n Y ≫ ℙ(ULift.{u} (Fin (n + 1)); Y) ↘ Y =
      𝔸(ULift.{u} (Fin n); Y) ↘ Y := by
  simp only [purityAffineProjectiveOpen, Category.assoc,
    ProjectiveSpace.standardOpenIso_inv_ι_over, AffineSpace.reindexIso_hom,
    AffineSpace.reindex_over]

variable {k : Type u} [Field k] {X Y : Over (Spec (.of k))}

/-- An affine open chart factoring a smooth map through affine space over its target. -/
structure PuritySmoothChart (f : X ⟶ Y) where
  source : Scheme.{u}
  inclusion : source ⟶ X.left
  dimension : ℕ
  etaleMap : source ⟶ 𝔸(ULift.{u} (Fin dimension); Y.left)
  isOpen_inclusion : IsOpenImmersion inclusion
  isAffine_source : IsAffine source
  isEtale_map : Etale etaleMap
  factorization : etaleMap ≫ 𝔸(ULift.{u} (Fin dimension); Y.left) ↘ Y.left =
    inclusion ≫ f.left

attribute [instance] PuritySmoothChart.isOpen_inclusion PuritySmoothChart.isAffine_source
  PuritySmoothChart.isEtale_map

namespace PuritySmoothChart
variable {f : X ⟶ Y} (c : PuritySmoothChart f)

/-- The chart domain as an object over the original field. -/
def sourceOver : Over (Spec (.of k)) := Over.mk (c.inclusion ≫ X.hom)

/-- The affine-space stage over the original field. -/
def affineOver : Over (Spec (.of k)) :=
  Over.mk (𝔸(ULift.{u} (Fin c.dimension); Y.left) ↘ Y.left ≫ Y.hom)

/-- The projective-space stage over the original field. -/
def projectiveOver : Over (Spec (.of k)) :=
  Over.mk (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left ≫ Y.hom)

def inclusionOver : c.sourceOver ⟶ X := Over.homMk c.inclusion rfl

def etaleOver : c.sourceOver ⟶ c.affineOver :=
  Over.homMk c.etaleMap (by
    change c.etaleMap ≫ (𝔸(ULift.{u} (Fin c.dimension); Y.left) ↘ Y.left ≫ Y.hom) = _
    rw [← Category.assoc, c.factorization, Category.assoc, Over.w]
    rfl)

def openOver : c.affineOver ⟶ c.projectiveOver :=
  Over.homMk (purityAffineProjectiveOpen c.dimension Y.left) (by
    exact purityAffineProjectiveOpen_over_assoc _ _ _)

def projectionOver : c.projectiveOver ⟶ Y :=
  Over.homMk (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left) rfl

instance : IsOpenImmersion c.inclusionOver.left := c.isOpen_inclusion
instance : Etale c.etaleOver.left := c.isEtale_map
instance : IsOpenImmersion c.openOver.left := inferInstanceAs
  (IsOpenImmersion (purityAffineProjectiveOpen c.dimension Y.left))
instance : IsProper c.projectionOver.left := inferInstanceAs
  (IsProper (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left))

instance [LocallyOfFiniteType X.hom] : LocallyOfFiniteType c.sourceOver.hom := by
  change LocallyOfFiniteType (c.inclusion ≫ X.hom)
  infer_instance
instance [IsSeparated X.hom] : IsSeparated c.sourceOver.hom := by
  change IsSeparated (c.inclusion ≫ X.hom)
  infer_instance
instance : QuasiCompact c.sourceOver.hom := by
  change QuasiCompact (c.inclusion ≫ X.hom)
  infer_instance

instance [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType c.affineOver.hom := by
  change LocallyOfFiniteType (𝔸(ULift.{u} (Fin c.dimension); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance
instance [IsSeparated Y.hom] : IsSeparated c.affineOver.hom := by
  change IsSeparated (𝔸(ULift.{u} (Fin c.dimension); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance
instance [QuasiCompact Y.hom] : QuasiCompact c.affineOver.hom := by
  change QuasiCompact (𝔸(ULift.{u} (Fin c.dimension); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance

instance [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType c.projectiveOver.hom := by
  change LocallyOfFiniteType (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance
instance [IsSeparated Y.hom] : IsSeparated c.projectiveOver.hom := by
  change IsSeparated (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance
instance [QuasiCompact Y.hom] : QuasiCompact c.projectiveOver.hom := by
  change QuasiCompact (ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left ≫ Y.hom)
  infer_instance

/-- The chart factorization as an equality in the category over the base field. -/
lemma factorization_over :
    c.etaleOver ≫ c.openOver ≫ c.projectionOver = c.inclusionOver ≫ f := by
  ext1
  change c.etaleMap ≫ purityAffineProjectiveOpen c.dimension Y.left ≫
    ℙ(ULift.{u} (Fin (c.dimension + 1)); Y.left) ↘ Y.left = c.inclusion ≫ f.left
  rw [purityAffineProjectiveOpen_over, c.factorization]

end PuritySmoothChart

/-- Smooth morphisms admit these charts around every point. -/
lemma exists_puritySmoothChart (f : X ⟶ Y) [Smooth f.left] (x : X.left) :
    ∃ c : PuritySmoothChart f, x ∈ Set.range c.inclusion := by
  obtain ⟨W, j, hj, hW, hx, n, e, he, hw⟩ := Smooth.exists_etale_affineSpace f.left x
  exact ⟨⟨W, j, n, e, hj, hW, he, hw⟩, hx⟩

/-- One chart for each point, to index a covering family without resizing. -/
def puritySmoothChartAt (f : X ⟶ Y) [Smooth f.left] (x : X.left) : PuritySmoothChart f :=
  (exists_puritySmoothChart f x).choose

lemma puritySmoothChartAt_covers (f : X ⟶ Y) [Smooth f.left] (x : X.left) :
    x ∈ Set.range (puritySmoothChartAt f x).inclusion :=
  (exists_puritySmoothChart f x).choose_spec

end AlgebraicGeometry
