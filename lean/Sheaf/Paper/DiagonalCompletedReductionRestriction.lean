/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Paper.DiagonalTowerLimitInterface

/-! # Finite reduction and completed scalar restriction

(blueprint: lem-sfb-diagonal-completed-reduction-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Simultaneous finite reduction commutes with exact completed scalar restriction,
including its quotient units, on all completed derived objects.

Source: Stacks 099I and 099M; blueprint diagonal tower limit proof, paragraph (3).
(blueprint: lem-sfb-diagonal-completed-reduction-restriction).
Proof: construct each ordinary reduction as the cokernel of multiplication by
ell^(n+1). Exact scalar restriction identifies these cokernels and their quotient
maps, naturally in the input and compatibly with the quotient transitions. Use
K-flat resolutions to derive the two simultaneous reduction functors. Restriction
preserves the regular resolving class, so uniqueness of pointwise left derived
functors gives the displayed natural isomorphisms. The ordinary cokernel square
identifies the localized quotient units with each other; descend the square through
the localization to obtain the stated equation on every derived object. -/
theorem diagonal_completed_reduction_restriction (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ W)] :
    let F := diagonalCompletedUnderlying ℓ W
    let E := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)).mapDerivedCategory
    let C := fun n : ℕ ↦
      ((evaluation ℕᵒᵖ (DiagonalCompleted ℓ W)).obj (op n)).mapDerivedCategory
    ∃ (M : DiagonalCompletedReduction ℓ W)
      (N : DiagonalCompletedReductionData ℓ (DiagonalMod ℓ W)),
      ∀ n : ℕ, ∃ α : M.derived.T ⋙ C n ⋙ F ≅ F ⋙ N.derived.T ⋙ E n,
        ∀ P : DerivedCategory (DiagonalCompleted ℓ W),
          F.map ((M.unit n).app P) ≫ α.hom.app P = (N.unit n).app (F.obj P) := by
  sorry

end AlgebraicGeometry.ProEtale
