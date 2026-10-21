/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps

/-! # Trace of the two Chern components of the diagonal

Source: blueprint lem-amb-p1-diagonal-integrals, proof steps 6--7
(blueprint: lem-amb-p1-diagonal-trace-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The projective-line trace sends the two Chern components of the diagonal to one.

Source: blueprint lem-amb-p1-diagonal-integrals, proof steps 6--7
(blueprint: lem-amb-p1-diagonal-trace-calculation).

Proof: the diagonal trace is the chart pushforward followed by the projective-line
trace `pr₂ ∘ b⁻¹` of def-amb-p1-trace (`projectiveLineDiagonalTrace_eq`). Compose the
hypothesis with that trace. The relative hyperplane summand goes to one by
`projectiveLineTrace_chern`. The decomposition `b` restricts to the shifted twisted unit
on the first summand, so the unit followed by `b⁻¹` is the first inclusion, and `pr₂`
kills it; hence the base summand goes to zero. The sum is the identity.
-/
theorem projectiveLine_diagonal_trace_calculation (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (a : Bool) :
    letI : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    letI : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
    ∀ (c : (ordinaryFinitePushforward A
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
      (ordinaryFiniteUnit A (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧),
    (projectiveLineDiagonalAlpha A S a ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map c ≫
        projectiveLineDiagonalChartPushforward N hN A hA S hS a =
      ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S)
          (projectiveLineTraceDatum N hN A hA (ProjectiveLine S)
            (ordinaryFiniteP1_isUnit N S hS)).chern +
        (projectiveLineTraceDatum N hN A hA S hS).chern ≫
          ordinaryFiniteP1Unit A N hA
            (projectiveLineTraceTransport N hN A hA) (ProjectiveLine S)
            (ordinaryFiniteP1_isUnit N S hS)) →
      projectiveLineDiagonalAlpha A S a ≫
        (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map c ≫
        projectiveLineDiagonalTrace N hN A hA S hS a =
      𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  intro c hc
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  have : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  have : IsNoetherian (ProjectiveLine S) := ⟨⟩
  have hunit : ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
        (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS) ≫
      projectiveLineTrace N hN A hA (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS) = 0 := by
    have hu : ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
        (ProjectiveLine S) (ordinaryFiniteP1_isUnit N S hS) =
        biprod.inl ≫ (projectiveLineTraceDatum N hN A hA (ProjectiveLine S)
          (ordinaryFiniteP1_isUnit N S hS)).decomposition.hom := by
      rw [(projectiveLineTraceDatum N hN A hA (ProjectiveLine S)
        (ordinaryFiniteP1_isUnit N S hS)).decomposition_hom, biprod.inl_desc]
    rw [hu, projectiveLineTrace, Category.assoc, Iso.hom_inv_id_assoc, biprod.inl_snd]
  have hc' := congrArg (· ≫ projectiveLineTrace N hN A hA (ProjectiveLine S)
    (ordinaryFiniteP1_isUnit N S hS)) hc
  simp only [Category.assoc, Preadditive.add_comp, projectiveLineTrace_chern, hunit,
    comp_zero, add_zero] at hc'
  rw [projectiveLineDiagonalTrace_eq]
  exact hc'

end AlgebraicGeometry.Etale
