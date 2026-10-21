/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.Paper.CompletionUnitModels

/-! # Canonical ordinary and derived models of the completion adjunction

Source: Stacks 07A6, 09T5, 0D6E, 0941 and the normalization refinement in
lem-trf-completion-unit-strict-quotient-model, steps 1--4.
(blueprint: lem-trf-completion-unit-canonical-models).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures.CompletionUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The ordinary tensor/limit adjunction and its derived comparison can be chosen
compatibly with the coherent coefficient calculus. This asserts the construction
and comparison normalizations only; it makes no assertion about the strict cone
augmentation or the completion unit formula.

Source: Stacks 03D7 (ordinary adjunction), 07A6 and 09T5 (derived adjunction), 0D6E
(composition), and 0941 (Roos), with steps 1--4 of
lem-trf-completion-unit-strict-quotient-model, an agent normalization refinement.
(blueprint: lem-trf-completion-unit-canonical-models).

Proof: Form the strict system whose nth term is scalar extension along the
completion projection and whose transition is the ordinary quotient adjunct.
The scalar-extension Hom bijections identify maps out of this system with
compatible families into the scalar restrictions; the limit universal property
gives its right adjoint. The unit is the family of pure tensors 1 tensor x.
Evaluation of the complex limit cone gives the canonical termwise comparison,
with its stated projections. The system construction is additive.

Choose a coherent calculus S by coefficientDerivedSystemEvaluationCalculus.
Derive the ordinary adjunction using flat-term K-flat representatives on the left
and K-injective representatives on the sequence site on the right. Factor the
right adjoint through exact scalar restriction and constant-ring inverse limit,
and transport the derived adjunction along the normalized composition comparison.
Both its left adjoint and S.reduction are left adjoint to coefficientSequenceLimit.
The unique adjunction-compatible isomorphism between these left adjoints transports
the universal left-derived comparison to reductionComparison. Transport preserves
its universal property and its invertibility on flat-term K-flat complexes.
The resolving Hom equation gives hom_normalization for every chain map.

To check reduction_evaluation, apply the finite scalar-extension Hom bijection to
the evaluated counit. S.counit_projection identifies its transpose with the actual
total-limit projection. The generic sequence comparison has the same projected
counit, and finite derived scalar extension has the same normalized K-flat
comparison. The two finite adjunction mates are therefore equal. On a flat-term
K-flat representative their equality is exactly reduction_evaluation. This is an
adjunction-mate computation, not detection of a derived map by its level values.
The chosen S and its coherence are retained throughout this transport.

Take the canonical right-derived unit of the constant tower limit and transport
through the termwise-limit comparison. It has the prescribed normalization on
K-injectives by the definition of rightDerivedFunctorObjQIso. Exact countable
products on the pro-etale site make the strict Roos cone a right-derived limit
model. Uniqueness of right-derived functors supplies roos, and its unit equation
is roos_normalization. The normalized derived composition theorem gives systemUnit
and its composition equation and proves that it is invertible on K-injective
systems; restriction is exact but need not preserve K-injectivity. These data form
M and D. Zero objects and zero complexes use the same universal properties; there
is no boundedness, completeness, or additional invertibility hypothesis on inputs. -/
theorem canonicalModels [∀ x : W, Invertible (l : W.residueField x)] :
    ∃ (S : CoefficientDerivedSystemCalculus l E W)
      (_coherence : CoefficientDerivedSystemCoherence l E W S)
      (M : OrdinaryModel l E W), Nonempty (DerivedModel l E W S M) := by
  sorry

end WeilConjectures.CompletionUnit
