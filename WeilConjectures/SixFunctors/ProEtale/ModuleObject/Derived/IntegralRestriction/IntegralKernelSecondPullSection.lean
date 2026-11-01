/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelSecondLineSection
public import WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullComparison
public import WeilConjectures.AlgebraicGeometry.RationalP1.Projective.ProjectivePullSectionCompatibility
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionTransportData
import all WeilConjectures.AlgebraicGeometry.RationalP1.Second.RationalP1SecondPullSectionCoreConjugate

import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # The two integral pullbacks agree on the diagonal -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients RationalP1
set_option allowUnsafeReducibility true in
attribute [local reducible] traceTate
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

attribute [local irreducible] twist square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The fixed integral comparison between the two pullbacks of q*K(1)[2].
Source: integral projective-line triangle calculation, paragraph (1).
(blueprint: lem-integral-kernel-second-pull-section). -/
@[irreducible]
def integralSecondPullComparison (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) Y)) :
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    let L := fun X ↦ spIntegralTwist X ℓ E
    let M := (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)
    (moduleObjectDerivedPullback Λ (firstProjection Y)).obj M ≅
      (moduleObjectDerivedPullback Λ (secondProjection Y)).obj M :=
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let A := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  pullTwistIso Λ (firstProjection Y) _ _
      (integralShiftedLinePullIso ℓ E (firstProjection Y)) A ≪≫
    (twist Λ (diagonalSurface Y) (spIntegralTwist (diagonalSurface Y) ℓ E)).mapIso
      ((ambientPullbackComparison Λ (square Y)).symm.app K) ≪≫
    (pullTwistIso Λ (secondProjection Y) _ _
      (integralShiftedLinePullIso ℓ E (secondProjection Y)) A).symm

/-- Forward projection with the integral comparison between the two pulled objects.
Source: integral projective-line triangle calculation, paragraph (1).
(blueprint: lem-integral-kernel-second-pull-section). -/
@[irreducible]
def integralSecondForwardProjection (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) Y)) :
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    let L := fun X ↦ spIntegralTwist X ℓ E
    let M := (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)
    M ⊗ (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
      (traceTate ℓ E (diagonalSurface Y)) ⟶
      (moduleObjectDerivedPushforward Λ (secondProjection Y)).obj
        ((twist Λ (diagonalSurface Y) (L (diagonalSurface Y))).obj
          ((moduleObjectDerivedPullback Λ (firstProjection Y)).obj M)) :=
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  projectionMap Λ (secondProjection Y) _ _ ≫
    (moduleObjectDerivedPushforward Λ (secondProjection Y)).map
      (tensorHom (integralSecondPullComparison ℓ E Y K).inv (𝟙 _) ≫
        (tensorShiftIso Λ (diagonalSurface Y) (spIntegralTwist (diagonalSurface Y) ℓ E)
          _).hom)

set_option maxHeartbeats 800000 in
-- Keep the fixed native pullback and twist comparisons folded during transport.
/-- The integral comparison restricts to the identity section equation.
Source: the second integral projective-line triangle, cancellation on the diagonal.
(blueprint: lem-integral-kernel-second-pull-section).
Proof: the untwisted comparison restricts to the two canonical section maps by
compositor associativity and the diagonal projection equations. The integral Tate
comparison has the same section equation by integralKernel_second_line_section.
The canonical tensor comparison is compatible with the section and is natural in
the line. Transport the untwisted equation through tensor and shift, using these
three equations, and cancel the two pull-twist comparisons. -/
theorem integralKernel_second_pull_section (Y : Scheme.{u})
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (Profinite.padicIntegersRingObj ℓ E.val) Y)) :
    let Λ := Profinite.padicIntegersRingObj ℓ E.val
    let L := fun X ↦ spIntegralTwist X ℓ E
    let M := (twist Λ (ProjectiveLine Y) (L (ProjectiveLine Y))).obj
      ((moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K)
    PullSectionCompatibility
      (moduleObjectDerivedPullback Λ (firstProjection Y))
      (moduleObjectDerivedPullback Λ (secondProjection Y))
      (moduleObjectDerivedPullback Λ (diagonalImmersion Y))
      (pullSectionIso Λ Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (pullSectionIso Λ Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)) M
      (integralSecondPullComparison ℓ E Y K).inv := by
  dsimp only
  let Λ := Profinite.padicIntegersRingObj ℓ E.val
  let F₁ := moduleObjectDerivedPullback Λ (firstProjection Y)
  let F₂ := moduleObjectDerivedPullback Λ (secondProjection Y)
  let G := moduleObjectDerivedPullback Λ (diagonalImmersion Y)
  let T := twist Λ (ProjectiveLine Y) (spIntegralTwist (ProjectiveLine Y) ℓ E)
  let U := twist Λ (diagonalSurface Y) (spIntegralTwist (diagonalSurface Y) ℓ E)
  let M := (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).obj K
  let s₁ := pullSectionIso Λ Y (firstProjection Y)
    (by unfold firstProjection; exact pullback.diagonal_fst _)
  let s₂ := pullSectionIso Λ Y (secondProjection Y)
    (by unfold secondProjection; exact pullback.diagonal_snd _)
  let eD := integralShiftedLinePullIso ℓ E (diagonalImmersion Y)
  let e₁ := pullTwistIso Λ (firstProjection Y) _ _
    (integralShiftedLinePullIso ℓ E (firstProjection Y)) M
  let e₂ := pullTwistIso Λ (secondProjection Y) _ _
    (integralShiftedLinePullIso ℓ E (secondProjection Y)) M
  let d := fun A ↦ pullTwistIso Λ (diagonalImmersion Y) _ _ eD A
  have h₁ : G.map e₁.hom ≫ (d (F₁.obj M)).hom ≫ T.map (s₁.hom.app M) =
      s₁.hom.app (T.obj M) :=
    pullTwist_section Λ Y (firstProjection Y) _ _ _ _ eD
      (integralKernel_second_line_section ℓ E Y (firstProjection Y) _) M
  have h₂ : G.map e₂.hom ≫ (d (F₂.obj M)).hom ≫ T.map (s₂.hom.app M) =
      s₂.hom.app (T.obj M) :=
    pullTwist_section Λ Y (secondProjection Y) _ _ _ _ eD
      (integralKernel_second_line_section ℓ E Y (secondProjection Y) _) M
  let b := (ambientPullbackComparison Λ (square Y)).symm.app K
  have data : PullSectionTransportData (G := G) (s₁ := s₁) (s₂ := s₂)
      T U M e₁ e₂ b := by
    refine { d₁ := d (F₁.obj M), d₂ := d (F₂.obj M), h₁ := ?_, h₂ := h₂, hb := ?_ }
    · change G.map e₁.inv ≫ s₁.hom.app (T.obj M) =
        (d (F₁.obj M)).hom ≫ T.map (s₁.hom.app M)
      rw [← h₁]
      simp only [← G.map_comp_assoc, e₁.inv_hom_id, G.map_id, Category.id_comp]
    · have hn := pullTwist_naturality Λ (diagonalImmersion Y) _ _ eD b.inv
      simpa only [Category.assoc, Functor.comp_obj, d, F₁, F₂, M] using
        congrArg (fun m ↦ G.map e₂.hom ≫ m ≫ T.map (s₁.hom.app M)) hn
  refine ⟨?_⟩
  unfold integralSecondPullComparison
  apply pull_section_transport T U M e₁ e₂ b data
  have hs := projective_square Λ Y K
  simp only [Iso.symm_inv, Iso.app_inv] at hs
  dsimp only [G, b, s₁, s₂, M]
  simp only [Iso.app_inv, Iso.symm_inv]
  rw [hs]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
