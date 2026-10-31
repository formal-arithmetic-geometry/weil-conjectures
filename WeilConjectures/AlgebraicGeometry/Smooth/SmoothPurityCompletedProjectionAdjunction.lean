/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos

/-! # Projection-normalized completed reduction adjunction

Source: latest blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence.proof.md.
(blueprint: lem-sp-completed-projection-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The ambient adjunction, normalized on its finite-level counit projections.
Source: current blueprint, sk-lem-sp-tower-equivalence.proof.md, Adjunction paragraph;
Stacks 0941 (blueprint: lem-sp-completed-projection-adjunction).

Proof: the completed coefficient projections form a cone to the ell-power ring-sheaf system. Apply
SheafOfModules.SequenceProjection.pushforwardLimitProjections to this cone. It constructs the
unbounded derived scalar-extension/total-limit adjunction and identifies each evaluated counit
with the scalar adjunct of the corresponding projection.

For the supplied R, compose its coefficient isomorphism with this cone. At each level, R.level and
the scalar-model object equality identify R.ordinary with the ordinary extension used by that
theorem. R.transition identifies their transitions on every local tensor generator. Tensor
generation gives one natural isomorphism of strict-system-valued functors, not merely unrelated
level isomorphisms. Its localization, R.universal, and uniqueness of left derived functors
identify the derived reduction with R.red. Exact restriction along R.coefficient transports the
source to completed modules. The inverse coefficient restriction is an exact inverse
equivalence, so it transports both the ordinary Hom bijection and its derived adjunction;
no tensor-flatness of a quotient ring is used.

The section and transition formulas of D.equivalence identify exact scalar forgetting with
spCompletedStrictTower. Uniqueness of the normalized right-derived limit identifies the right
adjoint with spCompletedTotalLimit, retaining each spCompletedTotalProjection. Transport the
adjunction through these natural isomorphisms. Scalar-adjoint uniqueness compares the evaluated
left functor with D.scalar at spCompletedEllCommProjection, giving e. The original counit
projection formula is then exactly the displayed equality by the definition of
spTowerReconstructionMap. Indeed, transpose the evaluated counit through the normalized
finite scalar adjunction. The counit projection law from the general theorem identifies its
transpose with the fixed total-limit projection. The Hom equivalence is injective, giving
the asserted equality after the canonical left-adjoint comparison e. No invertibility of that map,
normalization of C, or completeness of the
limit is used. -/
theorem spCompletedReduction_projectionAdjunction
    [HasCountableProducts
      (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) :
    ∃ adj : spCompletedReduction l E T D R ⊣ spCompletedTotalLimit l E T D,
      ∀ (C : spDerivedCoefficientTowers l E T D) (n : ℕ),
        ∃ e : (spDerivedCoefficientEvaluation l E T D n).obj
              ((spCompletedReduction l E T D R).obj
                ((spCompletedTotalLimit l E T D).obj C)) ≅
            (D.scalar (spCompletedEllCommProjection l E T n)).model.T.obj
              ((spCompletedTotalLimit l E T D).obj C),
          (spDerivedCoefficientEvaluation l E T D n).map (adj.counit.app C) =
            e.hom ≫ spTowerReconstructionMap l E T D C
              ((spCompletedTotalLimit l E T D).obj C)
              (Pi.lift (fun k : ℕ ↦ (spCompletedTotalProjection l E T D k).app C)) n := by
  sorry

end AlgebraicGeometry.ProEtale
