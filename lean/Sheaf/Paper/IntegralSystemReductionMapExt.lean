/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful

/-! Joint faithfulness of the finite quotient evaluations.

Source: Stacks 0941; coefficient-system maps are determined levelwise.
(blueprint: lem-pur-integral-system-reduction-map-ext)

A morphism of the derived coefficient system is a map of the sequence-site
complexes.  Equality can therefore be checked at each positive coefficient
level; the transition-compatible site maps are jointly conservative.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Finite evaluations jointly reflect equality after coherent reduction.

Source: Stacks 0941, levelwise description of a coefficient sequence.
(blueprint: lem-pur-integral-system-reduction-map-ext)

The coherent reduction is a derived category of transition-compatible
sequence-site complexes.  A morphism is determined by all of its coefficient
components, and the derived localization is applied componentwise.  Thus
levelwise equality of the evaluations implies equality of the original
morphism.
-/
theorem integralSystemReduction_map_ext
    {X : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    {A B : sfIntegralConstructibleCategory l E X}
    (p q : A ⟶ B)
    (h : ∀ n : ℕ,
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map p) =
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map q)) :
    (integralSystemReduction l E X).map p =
      (integralSystemReduction l E X).map q := by
  sorry

end WeilConjectures
