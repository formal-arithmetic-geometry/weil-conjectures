module

public import Sheaf.Paper.ConstantCompletionFiniteSystemModules

/-! The non-elementary flatness and tensor-reduction part of the finite constant
completion tower.
Source: Stacks Project, Tags 093M and 0912
(blueprint: new-p4-constant-completion-finite-system-flat-and-reduction).
The proof shows that taking sections of a constant sheaf is an exact functor of the
coefficient module, so it commutes with tensoring by finitely presented modules. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C]

/--
Source: Stacks Project, Tags 093M and 0912 (blueprint:
new-p4-constant-completion-finite-system-flat-and-reduction).
Proof: the scalar tower `htower` and the surjectivity of `A → A ⧸ I^(n+1)` force
`(Ideal.Quotient.mk _ a) • b = a • b`, so the given module structure is the canonical
one induced by the sheafification unit. Fix `R = A ⧸ I^(m+1)` and `U`, and let
`G(M)` be the sections over `U` of the sheafified constant presheaf with value the
`R`-module `M`; `G(R)` is `adicTerm … m U`. The functor `G` is additive and left exact
(constant presheaf and sheafification are exact, sections are left exact). It also
preserves surjections: a surjection of sets `p : M → N` has a set-theoretic section
`s`, and the constant sheaf of types (which commutes with forgetting the module
structure) sends `p ∘ s = id` to a splitting of `G(p)`. So `G` is exact, and the
natural map `M ⊗[R] G(R) → G(M)` is an isomorphism for finitely presented `M`
(compare both right exact functors on a presentation `R^a → R^b → M → 0`).
Flatness: for an ideal `𝔞` of the Noetherian ring `R`, `𝔞 ⊗[R] G(R) → G(R)` is
`G(𝔞) → G(R)`, injective by left exactness. Reduction: `G(R) ⊗[A] (A ⧸ I^(n+1))
= G(R) ⊗[R] (A ⧸ I^(min m n + 1)) ≅ G(A ⧸ I^(min m n + 1))`, which is
`adicTerm … (min m n) U`; on `b ⊗ mk a` this isomorphism is `a • adicTransition b`,
the transition being `G` of the quotient map. -/
theorem finiteSystem_flat_and_reduction (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [∀ (n : ℕ) (U : Cᵒᵖ), Module (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)]
    (htower : ∀ (n : ℕ) (U : Cᵒᵖ), IsScalarTower A (A ⧸ I ^ (n + 1))
      (adicTerm J A (finiteSystemUnder J A I) n U)) :
    (∀ (n : ℕ) (U : Cᵒᵖ),
      Module.Flat (A ⧸ I ^ (n + 1))
        (adicTerm J A (finiteSystemUnder J A I) n U)) ∧
    (∀ (m n : ℕ) (U : Cᵒᵖ),
      ∃ e : TensorProduct A (adicTerm J A (finiteSystemUnder J A I) m U)
          (A ⧸ I ^ (n + 1)) ≃ₗ[A] adicTerm J A (finiteSystemUnder J A I) (min m n) U,
        ∀ (b : adicTerm J A (finiteSystemUnder J A I) m U) (a : A),
          e (b ⊗ₜ[A] Ideal.Quotient.mk _ a) = a •
            adicTransition J A (finiteSystemUnder J A I) m (min m n)
              (Nat.min_le_left m n) U b) := by
  sorry
end CategoryTheory.ConstantCompletion
