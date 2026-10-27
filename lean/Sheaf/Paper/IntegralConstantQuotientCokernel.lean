/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T8
-/
module

public import Sheaf.Paper.PulledReductionComparisonData
public import Sheaf.Paper.BoundedConstructibleComplete

/-! # Constant principal quotients of arbitrary module sheaves

Source: current blueprint, det-lem-int-tensor-pullback, Comparison with the Stacks
Project; Stacks Tags 093J and 03EK.
(blueprint: lem-sfb-integral-constant-quotient-cokernel).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralAugmentedQuotient

/-- Constant ordinary tensor reduction is the sheaf cokernel of the uniformizer power,
with its actual quotient augmentation, for any constant-coefficient module sheaf.
Source: det-lem-int-tensor-pullback.proof.md, Comparison with the Stacks Project;
step 2 of lem-sfb-integral-augmented-quotient-towers; Stacks Tags 093J and 03EK
(blueprint: lem-sfb-integral-constant-quotient-cokernel).

Proof: write A for the lifted valuation ring and p for its uniformizer. The quotient
coefficient sheaf is the constant sheaf of A/(p^(n+1)); the prescribed finite-ring
comparison identifies its quotient map with OrderedExchange.quotient. The constant
section p^(n+1) acts naturally on every section module, defining the endomorphism mu.
Sheafification of the ordinary presheaf cokernel of mu is its sheaf cokernel. On a
site object the algebraic tensor-quotient isomorphism sends q(a) tensor x to the class
of a*x, and its inverse sends the class of x to 1 tensor x. The latter is well-defined
since q(p^(n+1)) is zero. The former is independent of the lift a since the difference
of two lifts is a p^(n+1) multiple. Additivity, balancing, and the two inverse identities
are the tensor relations. If a coefficient section is available only after
sheafification, apply these formulas on a covering where it lifts to the quotient
presheaf, then glue; uniqueness makes the formulas independent of that covering.
They commute with restrictions, so sheafification gives the asserted isomorphism.
The quotient projection maps x to 1 tensor x, which is the defining section formula
of the published ordinaryAugmentation. Equality on sections proves the normalization.
This uses sheaf cokernels, not surjectivity of quotient maps on arbitrary sections;
it applies also to zero modules, torsion modules, n=0 (exponent one), and empty objects.
-/
theorem constantQuotientCokernel
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W : Scheme.{u})
    (N : reductionModules W (exchangeConstantRing W (PbcIntegralRing l E))) (n : ℕ) :
    ∃ μ : End N,
      (∀ (Z : W.ProEtᵒᵖ) (x : N.val.obj Z),
        μ.val.app Z x =
          @SMul.smul ((exchangeConstantRing W (PbcIntegralRing l E)).obj.obj Z)
            (N.val.obj Z) inferInstance
            ((toSheafify (ProEt.topology W)
              ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (PbcIntegralRing l E)))).app Z
                ((pbcUniformizer l E) ^ (n + 1))) x) ∧
      ∃ c : cokernel μ ≅ ((OrderedExchange.reductionModule (pbcIntegralDatum l E) W).obj
          N).obj (op n),
        cokernel.π μ ≫ c.hom =
          ((OrderedExchange.ordinaryAugmentation (pbcIntegralDatum l E) W).app N).app
            (op n) := by sorry

end WeilConjectures.IntegralAugmentedQuotient
