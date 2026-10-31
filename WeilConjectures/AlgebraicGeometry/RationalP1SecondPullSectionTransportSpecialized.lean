/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1SecondPullSectionTransportData
public import WeilConjectures.AlgebraicGeometry.PullSectionTransport

/-! Specialization of the generic section transport to the rational projective-line square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] coefficient line twist firstProjection secondProjection square
attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- The generic transport calculation specialized to the two projective projections.
This is the tensor/shift part of the section argument after the ambient square
comparison has been expanded.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md,
Second identity, tensor and shift transport.
(blueprint: lem-sfb-rational-p1-second-pull-section-specialized).
Proof: instantiate `pull_section_transport` with the two fixed pullback functors,
the diagonal pullback, the Tate twist functors, and the supplied transport data. -/
theorem second_pull_section_transport_specialized
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [hproj : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [hdiag : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (data : PullSectionTransportData
      (F₁ := moduleObjectDerivedPullback (coefficient l c).X (firstProjection Y))
      (F₂ := moduleObjectDerivedPullback (coefficient l c).X (secondProjection Y))
      (G := moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y))
      (s₁ := pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _))
      (s₂ := pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _))
      (T := twist (coefficient l c).X (ProjectiveLine Y)
        (line l c (ProjectiveLine Y)))
      (U := twist (coefficient l c).X (diagonalSurface Y)
        (line l c (diagonalSurface Y)))
      (M := ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K))
      (e₁ := pullTwistIso (coefficient l c).X (firstProjection Y) _ _
        (shiftedLineComparison l c (firstProjection Y))
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K))
      (e₂ := pullTwistIso (coefficient l c).X (secondProjection Y) _ _
        (secondLineComparison l c k p hpl Y)
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K))
      (b := (ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K))
    (hbase : (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K).inv ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)) :
    (moduleObjectDerivedPullback (coefficient l c).X (diagonalImmersion Y)).map
        ((pullTwistIso (coefficient l c).X (firstProjection Y) _ _
          (shiftedLineComparison l c (firstProjection Y))
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K) ≪≫
        (twist (coefficient l c).X (diagonalSurface Y)
          (line l c (diagonalSurface Y))).mapIso
          ((ambientPullbackComparison (coefficient l c).X (square Y)).symm.app K) ≪≫
        (pullTwistIso (coefficient l c).X (secondProjection Y) _ _
          (secondLineComparison l c k p hpl Y)
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)).symm).inv) ≫
      (pullSectionIso (coefficient l c).X Y (firstProjection Y)
        (by unfold firstProjection; exact pullback.diagonal_fst _)).hom.app
        ((twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)) =
      (pullSectionIso (coefficient l c).X Y (secondProjection Y)
        (by unfold secondProjection; exact pullback.diagonal_snd _)).hom.app
        ((twist (coefficient l c).X (ProjectiveLine Y)
          (line l c (ProjectiveLine Y))).obj
          ((moduleObjectDerivedPullback (coefficient l c).X
          (ProjectiveLine Y ↘ Y)).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.RationalP1
