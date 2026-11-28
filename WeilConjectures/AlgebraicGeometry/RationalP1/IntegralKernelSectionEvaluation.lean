/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.First.FirstSectionKernelComposites
import WeilConjectures.AlgebraicGeometry.RationalP1.Native.NativeSectionTensorPrefix
import WeilConjectures.AlgebraicGeometry.RationalP1.FinishTensorEvaluation
import WeilConjectures.AlgebraicGeometry.RationalP1.SectionEvaluationCongruence

/-! # Evaluating an arbitrary kernel on the projective diagonal -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPushforward moduleObjectDerivedPullback
attribute [local irreducible] firstProjection secondProjection square
attribute [local irreducible] projectionMap singleUnitIso
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory




-- Compare the fixed native functor and tensor instances by structural congruence.
/-- The kernel-insertion prefix of the section evaluation, before the terminal functional. -/
private theorem kernel_section_evaluation_prefix
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N)
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion Λ Y M N α) ≫
      (firstPathComparison Λ Y).hom.app
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N)) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp) =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫
          (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) := by
  delta firstKernelInsertion
  section_evaluation_exact native_section_tensor_prefix Λ Y L d M N α hobj hp

/-- Cancellation of the first-projection transport before the terminal unitors. -/
private theorem kernel_section_evaluation_postprefix
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫
          (eqToIso d.p₁_canonical).hom.app N ≫
          eqToHom ((congrArg (fun F => F.obj N) d.p₁_canonical).symm.trans hobj))) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstNativeFunctional Λ Y L d N t) =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫ t)) := by
  unfold moduleObjectDerivedPushforward firstProjection at hobj ⊢
  have hcancel : (eqToIso d.p₁_canonical).hom.app N ≫
      eqToHom ((congrArg (fun F ↦ F.obj N) d.p₁_canonical).symm.trans hobj) ≫
      (eqToIso d.p₁_canonical).inv.app N ≫ t = t := by
    simp only [eqToHom_refl, Category.id_comp, Iso.hom_inv_id_app_assoc]
  unfold firstNativeFunctional
  dsimp only [id, moduleObjectDerivedPushforward, firstProjection]
  rw [← Functor.map_comp, ← MonoidalCategory.whiskerLeft_comp]
  simp only [Category.assoc]
  rw [hcancel]

-- Elaborate the native projection and the two canonical direct-image paths.
/-- The section evaluation before the terminal unitors. -/
private theorem kernel_section_evaluation_core
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X)
    (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion Λ Y M N α) ≫
      (firstPathComparison Λ Y).hom.app
        ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp) ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ firstNativeFunctional Λ Y L d N t) =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map (ρ_ M).inv ≫
      (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (M ◁ ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫
          d.support₁.hom ≫ d.R₁.R.map α ≫ t)) := by
  have hcanon : d.R₁.R = moduleObjectDerivedPushforward Λ
      (firstProjection Y) := by
    unfold moduleObjectDerivedPushforward firstProjection
    exact d.p₁_canonical
  have hobj : d.R₁.R.obj N =
      (moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N :=
    congrArg (fun F => F.obj N) hcanon
  rw [← Category.assoc, ← Category.assoc]
  rw [kernel_section_evaluation_prefix Λ Y L d M N α hobj hp]
  simpa only [Category.assoc] using
    (kernel_section_evaluation_postprefix Λ Y L d M N α t hobj)


/-- Evaluating a kernel arrow `α` on the projective diagonal: the direct image of the first
kernel insertion followed by the terminal first-projection functional of `t` is the direct
image of `M ◁ (support ≫ R₁ α ≫ t)` between unitors. -/
theorem kernel_section_evaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (d : Diagram Λ Y L)
    (M : DerivedCategory (Modules Λ (ProjectiveLine Y)))
    (N : DerivedCategory (Modules Λ (diagonalSurface Y)))
    (α : (DerivedCategory.singleFunctor (Modules Λ (diagonalSurface Y)) 0).obj
      (source Λ Y) ⟶ N)
    (t : d.R₁.R.obj N ⟶ unit Λ (ProjectiveLine Y))
    (hp : IsIso (projectionMap Λ (firstProjection Y) M N)) :
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
        (firstKernelInsertion Λ Y M N α) ≫
      firstTerminalFunctional Λ Y L d M N t hp =
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      ((ρ_ M).inv ≫ (M ◁
        ((singleUnitIso Λ (ProjectiveLine Y)).inv ≫ d.support₁.hom ≫
          d.R₁.R.map α ≫ t ≫ (singleUnitIso Λ (ProjectiveLine Y)).hom)) ≫
        (ρ_ M).hom) := by
  delta firstTerminalFunctional
  section_evaluation_exact finish_tensor_evaluation
    (moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)) M
    ((moduleObjectDerivedPushforward Λ (firstProjection Y)).obj N)
    (unit Λ (ProjectiveLine Y))
    ((moduleObjectDerivedPushforward Λ (ProjectiveLine Y ↘ Y)).map
      (firstKernelInsertion Λ Y M N α))
    ((firstPathComparison Λ Y).hom.app
      ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ⊗ N))
    (@inv _ _ _ _ (projectionMap Λ (firstProjection Y) M N) hp)
    (firstNativeFunctional Λ Y L d N t)
    (singleUnitIso Λ (ProjectiveLine Y)).inv
    d.support₁.hom (d.R₁.R.map α) t
    (singleUnitIso Λ (ProjectiveLine Y))
    (kernel_section_evaluation_core Λ Y L d M N α t hp)

end AlgebraicGeometry.ProEtale.RationalP1
