/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.Paper.OperationCoefficientActionData

/-! # A component of the operation coefficient reduction argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe d t u v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

/-- Integral compact-support reduction, finite quotient evaluation, site-perfect finite
Hom reduction, and integral scalar-extension evaluation: the parts of the operation
reduction argument that the library does not yet state.
Source: blueprint lem-fix-operation-reduction, proof steps 1, 2, 4 and 5;
Stacks 08J9, 0FPT; Bhatt--Scholze 6.7.2 and 6.8.14.

Proof: (1) Compact support. For a compactification `f = p ∘ j`, the integral
compact-support complex is the derived limit `M` of the tower of finite compact-support
images `K_n ↦ p_* j_! K_n`. Its reduction modulo `ϖ^{n+1}` is compared with `p_* j_! K_n`
by the projection `p` and the finite open-extension and proper direct-image coefficient
comparisons; these are isomorphisms because extension by zero is exact, the proper
direct image of a finite-Tor constructible complex commutes with the finite-free
coefficient change, and two derived limits of the same tower are isomorphic compatibly
with their projections. The same projections make the comparisons compatible with the
transition maps, and integral constructibility of `M` follows from that of the
reductions and a uniform cohomological bound (Bhatt--Scholze 6.8.14).
(2) Finite quotient evaluation. On flat-term K-flat representatives the quotient tensor
comparison sends `(x ⊗ a) ⊗ (y ⊗ b)` to `(x ⊗ y) ⊗ ab`; it preserves reassociation on pure
triples and the unit, hence by transposition the internal composition and evaluation
maps; repeated levels `m = n` give identities.
(3) Site-perfect Hom. For site-perfect `P`, ringed-site duality gives
`RHom(P, Q) ≅ P^∨ ⊗ Q` for arbitrary `Q`; the dual of a bounded complex of finite
projectives commutes with the quotient coefficient change termwise, and the
evaluation calculation identifies the result with the evaluation-defined reduction
map, which is therefore an isomorphism, locally and hence globally.
(4) Integral scalar extension `O_E → O_L` is finite free, so the same pure-tensor
calculation as in (2) gives its evaluation compatibility and Hom evaluation laws.
(blueprint: lem-fix-basic-operation-reduction-and-evaluation). -/
theorem basicOperationReductionAndEvaluation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X Y : Scheme.{u}) (f : X ⟶ Y) :
    (∀ (K₀ : Type u) [Field K₀] (hl₀ : IsUnit (l : K₀))
      [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
      [LocallyOfFiniteType (X ↘ Spec (.of K₀))]
      [QuasiCompact (X ↘ Spec (.of K₀))]
      [LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
      [QuasiCompact (Y ↘ Spec (.of K₀))]
      [f.IsOver (Spec (.of K₀))] [IsSeparated f]
      [LocallyOfFiniteType f] [QuasiCompact f]
      (c : Compactification f)
      (K : DerivedCategory (scalarReductionSource l E X))
      (hK : sfIntegralConstructible l E X K)
      (M : DerivedCategory (scalarReductionSource l E Y))
      (p : M ⟶ ∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n)
      (δ : (∏ᶜ fun n : ℕ ↦ sfCompactSupportTerm l E c K n) ⟶ M⟦(1 : ℤ)⟧)
      (hδ : IsDerivedLimitTriangle (sfCompactSupportTransition l E c K) M p δ),
      sfIntegralConstructible l E Y M ∧
        (∀ n : ℕ, IsIso (coefIntegralCompactSupportComparison l E c K M p n)) ∧
        ∀ n : ℕ,
          coefIntegralCompactSupportComparison l E c K M p (n + 1) ≫
              coefCompactSupportFiniteTransition l E c K n =
            sfCompactSupportReductionTransition l E Y M n ≫
              (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory.map
                (coefIntegralCompactSupportComparison l E c K M p n)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n),
      CoefficientEvaluationCompatible (finiteIntrinsicClosed l E W n)
        (finiteIntrinsicClosed l E W m) (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h) ∧
      FiniteHomEvaluation (finiteIntrinsicClosed l E W n) (finiteIntrinsicClosed l E W m)
        (coefficientFiniteQuotientDerived l E W h)
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose.quotientCalculus.tensor h)) ∧
    (∀ (W : Scheme.{u}) (m n : ℕ) (h : m ≤ n)
      (P Q : normalizedDVRDerived l E W n),
      IsProEtaleSitePerfect W (integralCoefficientCommRingSheaf l E W n) P →
      IsIso (finiteIntrinsicReductionHom l E W h P Q)) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
      [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L) (W : Scheme.{u}),
      CoefficientEvaluationCompatible (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W) ∧
      FiniteHomEvaluation (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
        (integralOrdinaryDerivedScalar l E L ι W) (scalarClosedTensor l E L ι W)) := by sorry

end WeilConjectures
