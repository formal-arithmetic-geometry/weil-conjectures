/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralOperationsWellDefined

/-!
# The specified inverse-image comparison is the completion unit

Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)--(3)
  (blueprint: lem-weil-isomorphism-derived-pullback-comparison-normalization).

For a scheme isomorphism `g : X ⟶ Y`, the specified comparison
`inverseImagePullbackComparisonDerived` from exact inverse image `G` to completed
integral pullback `P_g` is related to `G` of the actual completion unit
`S.adjunction.unit` of the canonical reduction/strict-system-limit calculus `S`
by a natural isomorphism `θ : P_g ≅ G ∘ completion`.  For a derived-complete object
the comparison is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

/-- The specified inverse-image comparison is normalized by the actual completion unit.
Source: literature/blueprint/main-20261015/blueprint/sec-trace-formula/
  sk-d-weil/prop-trf-rational-frobenius-integral-model.proof.md, clauses (2)--(3)
  (blueprint: lem-weil-isomorphism-derived-pullback-comparison-normalization).

The hypotheses bind the prime, the finite coefficient extension, the scheme
isomorphism and invertibility of `l` on both schemes.  `S` with `hS` is the canonical
calculus of `coefficientDerivedSystemEvaluationCalculus`: `S.reduction` is the
simultaneous derived reduction, left adjoint to the specified total limit
`coefficientSequenceLimit`, and `S.adjunction.unit` is the actual unit `u`.  The
conclusion gives one family `θ` of isomorphisms `P_g M ≅ G (L (R M))` with
`κ_M ≫ θ_M = G(u_M)` for every ambient `M` (an equality of whole derived morphisms),
naturality of `θ` in every derived morphism, and, for the derived-complete `N`, a
two-sided inverse `κinv` of `κ_N` with `κinv ≫ G(u_N) = θ_N`.

Proof, following the node:
1. Choose a flat-term K-flat resolution `q : Q → N` (`lem-pc-kflat-resolution`), the
   strict quotient tower `TQ = (Q ⊗ B_n)` and `D = U(TQ)`, `C_n = Res_n g^*Q_n`.  By
   `lem-weil-strict-roos-comparison` and exact countable products
   (`lem-weil-proetale-countable-products-exact`), `H(D) = Cone(1-s)[-1]` realizes the
   completion and `H(C)` realizes `P_g N`; `v_Q(z) = (0, (z ⊗ 1)_n)` is a chain map.
2. The derived-adjunction fraction formula (`lem-pc-pre-derived-adjoint-functors-general`)
   and the pushforward-composition comparison
   (`lem-weil-pbc-ringed-topoi-derived-pushforward-composition`) identify the actual unit
   `u_N` with `Q → V I → lim J`.
3. Hence `u_N = [v_Q][q]⁻¹` as whole cone maps, with zero shifted coordinate.
4. `G` is exact and preserves countable products
   (`lem-weil-proetale-isomorphism-inverse-image`), the coefficient maps commuting with
   all reductions.
5. Multiplication `j_n : g^*Q_n → G Q_n`, `x ⊗ a ↦ a x`, is an isomorphism of strict
   towers with inverse `x ↦ x ⊗ 1`.
6. `lem-cbc-exact-product-functor-strict-limit` gives `η_D : G H(D) ≅ H(G D)`, and
   `θ = η_D⁻¹ H(j)`.
7. The part (b) formula of `κ` and cancellation of `j_n` give `κ ≫ θ = G(u_N)`.
8. Chain-level squares descend to the derived category
   (`lem-pur-integral-operations-well-defined`): naturality and independence of `Q`.
9. For derived-complete `N`, `lem-weil-finite-free-completed-scalar-comparison` with
   `L = E` makes `u_N` invertible, so `κinv = θ ≫ G(u_N)⁻¹` inverts `κ_N`. -/
theorem isomorphismDerivedPullbackComparisonNormalization
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (hS : Nonempty (CoefficientDerivedSystemCoherence l E Y S))
    (N :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y))
    (hN : IsDerivedCompleteUnrestricted.{t, u} l E Y N) :
    ∃ θ : ∀ M :
      DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
        (integralTowerModules.{t, u} l E Y),
      (integralDerivedPullback l E g).obj M ≅
        (inverseImageIntegralDerived l E g).obj
          ((S.reduction ⋙ coefficientSequenceLimit l E Y).obj M),
      (∀ M :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y),
        inverseImagePullbackComparisonDerived l E g hX hY M ≫
            (θ M).hom =
          (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app M)) ∧
      (∀ (M M' :
        DerivedCategory.{max (t + 2) (u + 1), max (t + 1) u, max (t + 2) (u + 1)}
          (integralTowerModules.{t, u} l E Y))
        (f : M ⟶ M'),
        (integralDerivedPullback l E g).map f ≫ (θ M').hom =
          (θ M).hom ≫
            (inverseImageIntegralDerived l E g).map
              ((S.reduction ⋙ coefficientSequenceLimit l E Y).map f)) ∧
      ∃ κinv : (integralDerivedPullback l E g).obj N ⟶
          (inverseImageIntegralDerived l E g).obj N,
        κinv ≫ inverseImagePullbackComparisonDerived l E g hX hY N =
            𝟙 _ ∧
          inverseImagePullbackComparisonDerived l E g hX hY N ≫ κinv =
            𝟙 _ ∧
          κinv ≫ (inverseImageIntegralDerived l E g).map (S.adjunction.unit.app N) =
            (θ N).hom := by
  sorry

end WeilConjectures
