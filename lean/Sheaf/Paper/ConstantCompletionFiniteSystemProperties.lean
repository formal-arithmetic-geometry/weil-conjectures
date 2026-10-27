module
public import Sheaf.Paper.ConstantCompletionFiniteSystemModules
/-! Flatness and reduction data for the finite constant completion tower.
Source: Stacks Project, Tags 093M and 0912
(blueprint: new-e2-constant-completion-finite-system-properties).
The sectionwise finite quotient tower has flat terms, surjective transitions, and the
standard tensor reduction equivalences. -/
@[expose] public noncomputable section
set_option linter.style.haveILetI false
set_option linter.style.longLine false
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]
/--
Source: Stacks Project, Tags 093M and 0912
(blueprint: new-e2-constant-completion-finite-system-properties).
Proof: the finite constant quotient sections are flat over their coefficient
quotients; quotient maps give surjective transitions; and the canonical reduction
maps identify tensoring a stage by `A/I^(n+1)` with the `min` stage, with the stated
scalar formula. These are the hypotheses of the sectionwise adic algebra limit
argument.
-/
theorem finiteSystem_properties (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)] :
    (∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (n : ℕ) (U : Cᵒᵖ), Module.Flat (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (n : ℕ) (U : Cᵒᵖ),
      Function.Surjective (adicTransition J A (finiteSystemUnder J A I) (n + 1) n
        (Nat.le_succ n) U)) ∧
    (∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A (finiteSystemUnder J A I) m U)
          (A ⧸ I ^ (n + 1)) ≃ₗ[A] adicTerm J A (finiteSystemUnder J A I) (min m n) U,
        ∀ (b : adicTerm J A (finiteSystemUnder J A I) m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) = a •
            adicTransition J A (finiteSystemUnder J A I) m (min m n)
              (Nat.min_le_left m n) U b) := by
  sorry
end CategoryTheory.ConstantCompletion
