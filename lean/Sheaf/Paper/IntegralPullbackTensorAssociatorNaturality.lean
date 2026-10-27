/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CompletedPullbackTensorComparison
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.IntegralSystemReductionFullyFaithful

/-! # Naturality of the normalized integral tensor associator

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS, 07A4,
0941 and 0FPQ; the representative-independent derived naturality specialization
of the normalized completed associator.
(blueprint: lem-pur-integral-tensor-associator-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace WeilConjectures

/-- Naturality of the normalized integral tensor associator on arbitrary derived
morphisms.

Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS, 07A4,
0941 and 0FPQ (blueprint: lem-pur-integral-tensor-associator-naturality).

Proof: coherent reduction is a functor with a natural reduction/tensor
comparison.  The nested comparison squares for the two bracketings follow from
the naturality of this comparison.  The defining reduction equation for the
normalized integral associator identifies both bracketings with the associator
of the strict coefficient-system monoidal structure.  That strict associator is
natural in all three variables.  Applying the faithful coherent reduction and
cancelling the comparison isomorphisms reflects the equality.  The completed
tensor and its action on pairs of morphisms preserve the derived-complete
constructible category, so the equation applies to arbitrary integral arrows,
including identities, zero arrows, and zero objects.
-/
theorem pullbackTensorIntegralAssociator_naturality
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    {M N P M' N' P' : sfIntegralConstructibleCategory l E W}
    (f : M ⟶ M') (g : N ⟶ N') (h : P ⟶ P') :
    (constructibleIntegralTensor l E W).map
        (Prod.mkHom ((constructibleIntegralTensor l E W).map (Prod.mkHom f g)) h) ≫
        (pullbackTensorIntegralAssociator l E W M' N' P').hom =
      (pullbackTensorIntegralAssociator l E W M N P).hom ≫
        (constructibleIntegralTensor l E W).map
          (Prod.mkHom f ((constructibleIntegralTensor l E W).map (Prod.mkHom g h))) := by
  sorry

end WeilConjectures
