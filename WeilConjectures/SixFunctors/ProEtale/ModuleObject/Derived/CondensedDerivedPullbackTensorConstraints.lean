/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedTensorKoszulSymmetry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPullbackTensorKoszul

/-! # Canonical condensed derived pullback tensor constraints

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/def-weil-derived-pullback-tensor-hom.md, direct
condensed-coefficient derived pullback and K-flat relative tensor paragraphs
(blueprint: lem-pur-derived-pullback-tensor-constraints).

## Main statements

* `AlgebraicGeometry.ProEtale.CondensedRing.derivedPullbackTensorConstraints`: the
  associativity, left and right unit, and Koszul-symmetry equations of the canonical
  comparisons `μ = leftDerivedUpperStarTensorIso` and `e = leftDerivedUpperStarUnitIso`
  of the derived pullback `Lf^*` of condensed module objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
open scoped CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical tensor, unit, and symmetry coherence equations for derived pullback.

This packages the comparison isomorphism and unit comparison supplied by the
strong-monoidality theorem for condensed module objects.
(blueprint: lem-pur-derived-pullback-tensor-constraints) -/
theorem derivedPullbackTensorConstraints
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K N M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
    (((leftDerivedUpperStarTensorIso Λ f).app
        (MonoidalCategoryStruct.tensorObj K N)).app M).hom ≫
        MonoidalCategoryStruct.whiskerRight
          (((leftDerivedUpperStarTensorIso Λ f).app K).app N).hom
          (L((f)^*⟦Λ⟧).obj M) ≫
        (MonoidalCategoryStruct.associator
          (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N) (L((f)^*⟦Λ⟧).obj M)).hom =
      (L((f)^*⟦Λ⟧).map
          (MonoidalCategoryStruct.associator K N M).hom) ≫
        (((leftDerivedUpperStarTensorIso Λ f).app K).app
          (MonoidalCategoryStruct.tensorObj N M)).hom ≫
        MonoidalCategoryStruct.whiskerLeft
          (L((f)^*⟦Λ⟧).obj K)
          (((leftDerivedUpperStarTensorIso Λ f).app N).app M).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app
          (MonoidalCategoryStruct.tensorUnit _)).app K).hom ≫
      MonoidalCategoryStruct.whiskerRight
          (leftDerivedUpperStarUnitIso Λ f).hom
          (L((f)^*⟦Λ⟧).obj K) ≫
      (MonoidalCategoryStruct.leftUnitor (L((f)^*⟦Λ⟧).obj K)).hom =
      L((f)^*⟦Λ⟧).map (MonoidalCategoryStruct.leftUnitor K).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app K).app
          (MonoidalCategoryStruct.tensorUnit _)).hom ≫
      MonoidalCategoryStruct.whiskerLeft
          (L((f)^*⟦Λ⟧).obj K)
          (leftDerivedUpperStarUnitIso Λ f).hom ≫
      (MonoidalCategoryStruct.rightUnitor (L((f)^*⟦Λ⟧).obj K)).hom =
      L((f)^*⟦Λ⟧).map (MonoidalCategoryStruct.rightUnitor K).hom ∧
    (((leftDerivedUpperStarTensorIso Λ f).app K).app N).hom ≫
      (CategoryTheory.derivedTensorKoszulSymmetry _
        (L((f)^*⟦Λ⟧).obj K) (L((f)^*⟦Λ⟧).obj N)).hom =
      L((f)^*⟦Λ⟧).map
          (CategoryTheory.derivedTensorKoszulSymmetry _ K N).hom ≫
        (((leftDerivedUpperStarTensorIso Λ f).app N).app K).hom := by
  let := leftDerivedUpperStarOplaxMonoidal Λ f
  have hδ (A B : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))) :
      Functor.OplaxMonoidal.δ L((f)^*⟦Λ⟧) A B =
        (((leftDerivedUpperStarTensorIso Λ f).app A).app B).hom := by
    rfl
  have hη : Functor.OplaxMonoidal.η L((f)^*⟦Λ⟧) =
      (leftDerivedUpperStarUnitIso Λ f).hom := by
    exact leftDerivedUpperStarOplaxMonoidal_η Λ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hδ] using
      (Functor.OplaxMonoidal.associativity L((f)^*⟦Λ⟧) K N M)
  · simpa only [hδ, hη] using
      (Functor.OplaxMonoidal.left_unitality_hom L((f)^*⟦Λ⟧) K)
  · simpa only [hδ, hη] using
      (Functor.OplaxMonoidal.right_unitality_hom L((f)^*⟦Λ⟧) K)
  · exact condensedPullbackTensorKoszul Λ f K N

end AlgebraicGeometry.ProEtale.CondensedRing
