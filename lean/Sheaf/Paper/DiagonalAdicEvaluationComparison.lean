/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Paper.DiagonalTowerLimitInterface

/-! # Finite reduction of the normalized total limit

(blueprint: lem-sfb-diagonal-adic-evaluation-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Reduction of a total limit of derived quotient towers is naturally evaluation;
the comparison is the adjoint of the actual limit projection.

Source: Stacks 099M; blueprint diagonal tower limit proof, paragraph (3), and
`lemma-weil-pbc-adic-completion-reduction`.
(blueprint: lem-sfb-diagonal-adic-evaluation-comparison).
Proof: identify D's ordinary cokernel tower with the strict scalar quotient tower.
Uniqueness of its pointwise left derived functor identifies D.T with the K-flat
quotient model; uniqueness of total right derived limits identifies L.R and its
projections with the normalized adic completion model. The finite quotient is
perfect, with the two-term resolution by multiplication by ell^(n+1). The adic
completion reduction theorem makes the adjoint of each projection an isomorphism.
Uniqueness of the pointwise left derived quotient identifies any normalized N with
this same finite reduction. Transport the evaluation-adjoint comparison through
these identifications. Its adjunction unit formula gives the displayed equation,
and functoriality on K-flat representatives descends to a natural isomorphism on
the entire integral derived category. -/
theorem diagonal_adic_evaluation_comparison (ℓ : ℕ) [Fact ℓ.Prime]
    (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ W)]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ W))
    (hcompletion : DiagonalCompletionSpec ℓ W D)
    (L : DiagonalRlim (DiagonalMod ℓ W))
    (N : DiagonalCompletedReductionData ℓ (DiagonalMod ℓ W)) (n : ℕ) :
    let E := ((evaluation ℕᵒᵖ (DiagonalMod ℓ W)).obj (op n)).mapDerivedCategory
    ∃ β : D.T ⋙ L.R ⋙ N.derived.T ⋙ E ≅ D.T ⋙ E,
      ∀ K : DerivedCategory (DiagonalAb W),
        (N.unit n).app (L.R.obj (D.T.obj K)) ≫ β.hom.app K =
          (L.projection n).app (D.T.obj K) := by
  sorry

end AlgebraicGeometry.ProEtale
