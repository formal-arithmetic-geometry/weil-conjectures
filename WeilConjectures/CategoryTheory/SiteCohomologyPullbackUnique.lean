/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB

/-! # Uniqueness of normalized pullback on object cohomology

Source: Stacks Project, Derived Categories, Tag 015B (4), and Homology, Tag 010T.
(blueprint: lem-weil-pbc-site-cohomology-pullback-unique)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- Normalization and compatibility with connecting maps determine the family uniquely.

Source: Stacks Project, Derived Categories, Tag 015B (4), and Homology, Tag 010T.
(blueprint: lem-weil-pbc-site-cohomology-pullback-unique)

Proof: Degree zero is determined by evaluation on the generator of the free abelian
sheaf on V. For the induction step embed A into an injective I and let Q be its
cokernel. Positive Ext into I vanishes, so the boundary from H^n(V,Q) onto
H^{n+1}(V,A) is surjective. Both families commute with this boundary; the induction
hypothesis applied to Q therefore equates their values on every class. -/
theorem siteCohomology_pullback_unique {C D : Type u}
    [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (U : C ⥤ D)
    [U.IsContinuous J K] [(sheafPullback U AddCommGrpCat.{u} J K).Additive]
    [PreservesFiniteLimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [PreservesFiniteColimits (sheafPullback U AddCommGrpCat.{u} J K)]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})] [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]
    (f g : SiteCohomologyFamily J K U)
    (hf : SiteCohomologyFamily.IsPullback J K U f)
    (hg : SiteCohomologyFamily.IsPullback J K U g) : f = g := by
  funext n V A
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  induction n generalizing A with
  | zero =>
    apply Sheaf.objectCohomologyEval₀_injective K (U.obj V) _
    exact (hf.2.2 V A x).trans (hg.2.2 V A x).symm
  | succ n ih =>
    let S : ShortComplex (Sheaf J AddCommGrpCat.{u}) :=
      ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    have hS' := hS.map_of_exact (sheafPullback U AddCommGrpCat.{u} J K)
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁
      ((presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj V ⋙ AddCommGrpCat.free))
      hS x (Abelian.Ext.eq_zero_of_injective _) rfl
    rw [← hy, hf.2.1 S hS hS' n V y, hg.2.1 S hS hS' n V y, ih S.X₃ y]

end CategoryTheory
