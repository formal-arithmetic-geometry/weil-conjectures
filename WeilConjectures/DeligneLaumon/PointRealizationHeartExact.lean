/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.PointRealizationStandardCohomology
import WeilConjectures.CategoryTheory.Triangulated.TStructure.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-! # Exact restriction of point comparison data to full hearts

Source: BBD 1.3.3--1.3.6 (blueprint: lem-a1-point-realization-heart-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe uC vC uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
namespace WeilConjectures


variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B]
  [HasShift B ℤ] [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
  [IsTriangulated B]
  {t : TStructure C} {s : TStructure B} {F : C ⥤ B}

omit [IsTriangulated C] [IsTriangulated B] in
/-- T-exactness sends the source heart into the target heart.
Source: BBD 1.3.3 (blueprint: lem-a1-point-realization-heart-exact). -/
theorem pointRealization_mem_heart (d : PointRealizationComparison t s F)
    (K : C) (hK : t.heart K) : s.heart (F.obj K) := by
  let := d.tExact
  obtain ⟨_, _⟩ := (t.mem_heart_iff K).1 hK
  exact (s.mem_heart_iff _).2
    ⟨Functor.IsTExact.isLE_obj t s F K 0, Functor.IsTExact.isGE_obj t s F K 0⟩

/-- Restrict the specified t-exact functor to the full hearts.
Source: BBD 1.3.3--1.3.6 (blueprint: lem-a1-point-realization-heart-exact). -/
def pointRealizationHeartFunctor (d : PointRealizationComparison t s F) :
    t.heart.FullSubcategory ⥤ s.heart.FullSubcategory :=
  s.heart.lift (t.heart.ι ⋙ F) (fun K ↦ pointRealization_mem_heart d K.obj K.property)

/-- The heart restriction of the specified exact t-exact functor is exact.
Source: BBD 1.3.3--1.3.6 and the heart short-exact/triangle criterion
(blueprint: lem-a1-point-realization-heart-exact).
Proof: t-exactness preserves hearts. Turn a short exact heart sequence into a
distinguished triangle, apply the exact functor, and turn its image back into a
short exact sequence. The additive exactness criterion gives both finite limits
and finite colimits. This works also for zero hearts and the zero functor. -/
theorem pointRealizationHeart_exact (d : PointRealizationComparison t s F) :
    PreservesFiniteLimits (pointRealizationHeartFunctor d) ∧
      PreservesFiniteColimits (pointRealizationHeartFunctor d) := by
  let := d.commShift
  let := d.exact
  let := t.hasHeartFullSubcategory
  let := s.hasHeartFullSubcategory
  let := CategoryTheory.Triangulated.TStructure.abelianHeart t t.heart.FullSubcategory
  let := CategoryTheory.Triangulated.TStructure.abelianHeart s s.heart.FullSubcategory
  let H := pointRealizationHeartFunctor d
  have : H.Additive :=
    { map_add := by
        intro X Y f g
        apply s.heart.ι.map_injective
        exact F.map_add }
  apply ((Functor.exact_tfae H).out 0 3).1
  intro S hS
  obtain ⟨δ, hδ⟩ := (t.shortExact_iff_exists_distTriang S).1 hS
  apply (s.shortExact_iff_exists_distTriang _).2
  exact ⟨F.map δ ≫ (F.commShiftIso (1 : ℤ)).hom.app _, F.map_distinguished _ hδ⟩


end WeilConjectures
