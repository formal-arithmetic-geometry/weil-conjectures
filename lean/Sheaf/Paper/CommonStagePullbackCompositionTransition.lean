/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CommonStagePullbackCompNaturality

/-! # Transition step for common pullback composition

This is the stage-enlargement naturality substep used before identifying the
finite-stage compositor representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients
namespace WeilConjectures

/-- Naturality of the normalized pullback compositor along the canonical map from
an object to its representative at a larger coefficient stage.

Source: Stacks Tag 099N(5), the naturality step in the common-stage composition
construction. This specializes the existing representative naturality theorem
to the identity arrow at the enlarged coefficient stage. -/
theorem commonStagePullbackCompComponent_transition
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L)
    (r : M.toStage hM ⟶ (⟨L, M.toStage hM⟩ :
      generalAlgebraicallyClosedConstructibleCategory l Ω Y).toStage le_rfl) :
    (commonStageDerivedPullback l Ω (h ≫ f)).map
        (ofHom M ⟨L, M.toStage hM⟩ L hM le_rfl r) ≫
        (commonStagePullbackCompComponent l Ω h f ⟨L, M.toStage hM⟩).hom =
      (commonStagePullbackCompComponent l Ω h f M).hom ≫
        (commonStageDerivedPullback l Ω h).map
          ((commonStageDerivedPullback l Ω f).map
            (ofHom M ⟨L, M.toStage hM⟩ L hM le_rfl r)) := by
  exact commonStagePullbackCompComponent_naturality l Ω h f
    (ofHom M ⟨L, M.toStage hM⟩ L hM le_rfl r)

end WeilConjectures
