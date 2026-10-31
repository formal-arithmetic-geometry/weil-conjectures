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

/-! # Evaluating an arbitrary kernel on the projective diagonal

Source: the first identity in the rational projective-line triangle proof, the section
and projection calculation after the trace has been transported to the first projection.
(blueprint: lem-integral-kernel-section-evaluation).
-/

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




set_option maxHeartbeats 800000 in
-- Compare the fixed native functor and tensor instances by structural congruence.
/-- The kernel-insertion prefix before the terminal first-projection functional.
Source: the pre-unitor section calculation in the rational projective-line triangle
(blueprint: lem-integral-kernel-section-evaluation).
This is the strict prefix of `first_section_tensor_evaluation_core`, before any
terminal functional. Proof: expand the kernel insertion and use naturality of the
path comparison to move its second-direct-image map to the first path. Compatibility
of the canonical pullback composition comparisons with the two diagonal sections
identifies the transported section with the first-projection section. The section
case of projection/composition coherence identifies the inverse diagonal tensor map
with the right-unitor inverse, the supported coefficient insertion, and the first
projection map. Projection naturality then replaces the supported coefficient arrow
by its composite with α. The normalization of d.support₁ and the full derived unit
d.p₁_unit identify this coefficient insertion with d.support₁.hom transported by
d.p₁_canonical. Apply the outer direct image and cancel the first projection map
against its specified inverse hp. The final eqToHom changes only the presentation
of its target object, using hobj. -/
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

/-- Cancellation of the first-projection transport before the terminal unitors.
Source: the first identity in the rational projective-line triangle proof
(blueprint: lem-integral-kernel-section-evaluation).
Proof: the object-equality loop gives the identity morphism by proof irrelevance.
The forward and inverse components of eqToIso d.p₁_canonical then cancel. Combine
the two direct-image maps and the two left whiskerings by functoriality, reassociate,
and apply this morphism cancellation. This uses no property of the kernel arrow or
of the functional, and no section/projection or trace identity. -/
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

set_option maxHeartbeats 800000 in
-- Elaborate the native projection and the two canonical direct-image paths.
/-- The section/projection paste before the terminal unitors.
Source: the first identity in the rational projective-line triangle proof, with the
terminal unitors omitted (blueprint: lem-integral-kernel-section-evaluation).
Proof: path-comparison naturality moves the kernel insertion across the path change;
projectionMap naturality cancels the specified inverse first projection. The diagonal
section identity leaves the normalized supported arrow followed by the native
functional. -/
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


/-- The section calculation with an arbitrary kernel arrow and an arbitrary functional.
It uses neither a Tate pullback comparison nor a trace base-change equation. In particular,
no integration equation for `d` is used.

Source: current blueprint, sec-six-functors-basics/sk-prop-p1-adjunction-rational/
sk-prop-p1-adjunction-rational-triangle.proof.md, First identity, final three sentences
(blueprint: lem-integral-kernel-section-evaluation).

Proof: apply the existing pre-unitor evaluation to the arbitrary kernel and functional.
Postcompose it by the direct image of identity_M tensor singleUnitIso.hom, and then by
the right unitor. Functoriality, tensor functoriality and associativity combine the
resulting word into the displayed right-hand side. These elementary rewrites take
place in the proved private categorical helper. Explicit congruence proofs identify
the native instance expressions with that helper's expressions, avoiding expensive
kernel conversion. The argument works for zero kernels and zero functionals and uses
invertibility only of the specified projection at N. -/
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
