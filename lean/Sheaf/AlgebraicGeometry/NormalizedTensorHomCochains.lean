/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Sheaf.Algebra.Homology.HomTensorDegreewise
public import Sheaf.Algebra.Homology.NormalizedHomComplexGlobalCochains
import Sheaf.Algebra.Homology.HomTensorDifferential

/-! # Normalized tensor-Hom comparison on ordinary cochains

Source: Stacks Project, Cohomology on Sites, Tags 0A90 and 0A8Z.
(blueprint: lem-pc-normalized-tensor-hom-cochains).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex
namespace AlgebraicGeometry

/-- The explicitly constructed uncurrying equivalence on ordinary cochains.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochains). -/
def normalizedTensorHomCochains (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k : ℤ) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    Cochain P (homComplex (R := X.sheaf) L I) k ≃+
      Cochain (pullbackTensorTotal X P L) I k := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let H := homComplex (R := X.sheaf) L I
  let T := pullbackTensorTotal X P L
  let a := homTensorDegreewiseMap X.sheaf P L I k
  letI : IsIso a := (homTensorDegreewiseMap_spec X.sheaf P L I k).2
  let b : (SheafOfModules.unit (moduleRings X.toRingedSpace) ⟶
        (homComplex (R := X.sheaf) P H).X k) ≃+
      (SheafOfModules.unit (moduleRings X.toRingedSpace) ⟶
        (homComplex (R := X.sheaf) T I).X k) :=
    { toFun s := s ≫ a
      invFun s := s ≫ inv a
      left_inv s := by simp [Category.assoc]
      right_inv s := by simp [Category.assoc]
      map_add' s t := by simp only [Preadditive.add_comp] }
  exact (normalizedHomGlobalCochains X.sheaf P H k).symm.trans
    (b.trans (normalizedHomGlobalCochains X.sheaf T I k))

set_option maxHeartbeats 800000 in
-- Elaborating the composite sheaf and tensor comparisons exceeds the default heartbeat limit.
/-- The uncurrying equivalence commutes with the ordinary cochain differential.
Source: Stacks Project, sites-cohomology.tex, Tag 0A90 (lemma-compose).
(blueprint: lem-pc-normalized-tensor-hom-cochains).
Proof: the explicit global-cochain comparisons commute with the differential.
Between them, postcomposition by the degreewise uncurrying map commutes with
the differential by `homTensorDegreewiseMap_comm`. Apply the global comparison
on the left to verify the corresponding equality for its inverse, and compose
the three equalities. -/
theorem normalizedTensorHomCochains_comm (X : Scheme.{u})
    (P L I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (k m : ℤ) (c : Cochain P (homComplex (R := X.sheaf) L I) k) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    normalizedTensorHomCochains X P L I m (δ k m c) =
      δ k m (normalizedTensorHomCochains X P L I k c) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  let H := homComplex (R := X.sheaf) L I
  let T := pullbackTensorTotal X P L
  have hs : (normalizedHomGlobalCochains X.sheaf P H m).symm (δ k m c) =
      (normalizedHomGlobalCochains X.sheaf P H k).symm c ≫
        (homComplex (R := X.sheaf) P H).d k m := by
    apply (normalizedHomGlobalCochains X.sheaf P H m).injective
    rw [AddEquiv.apply_symm_apply, normalizedHomGlobalCochains_comm,
      AddEquiv.apply_symm_apply]
  change normalizedHomGlobalCochains X.sheaf T I m
      ((normalizedHomGlobalCochains X.sheaf P H m).symm (δ k m c) ≫
        homTensorDegreewiseMap X.sheaf P L I m) = _
  rw [hs, Category.assoc, ← homTensorDegreewiseMap_comm, ← Category.assoc]
  exact normalizedHomGlobalCochains_comm X.sheaf T I k m
    ((normalizedHomGlobalCochains X.sheaf P H k).symm c ≫
      homTensorDegreewiseMap X.sheaf P L I k)

end AlgebraicGeometry
