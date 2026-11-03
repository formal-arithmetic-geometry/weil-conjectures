/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerIntegralCriterion

import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeNormalizedLimitEffectivity
import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeConstructibleReductionsResidue

/-! # Native normalized tower counit and integral-criterion inputs

Source: current sk-lem-sp-tower proof, second paragraph and plan steps 3--5.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)

private theorem evaluated_counit_isIso
    (L : Limit l E T D R) (C : spDerivedCoefficientTowers l E T D)
    (h : IsIso (L.adjunction.counit.app C)) (n : ℕ) :
    IsIso ((spDerivedCoefficientEvaluation l E T D n).map
      ((redLimitAdjunction l E T D R L).counit.app C)) := by
  have := h
  rw [redLimitAdjunction, Adjunction.comp_counit_app]
  infer_instance

/-- The actual total limit of a normalized constructible finite-Tor tower is
canonically uniformizer-complete, has bounded constructible first uniformizer
reduction, and has invertible evaluated counit. These are the inputs to the native
integral criterion, rather than a legacy integral constructibility predicate.
Source: current blueprint sk-lem-sp-tower, second paragraph; Stacks 0940
(blueprint: lem-sp-native-tower-residue-counit).

Proof: use ell=u*pi^e and the regular coefficient-fibre identification. On a strict
simultaneous flat-term K-flat representative, the generic quotient-error triangle
identifies the error on the tail n>=m with the shifted constant C_m tower whose
successor transitions are multiplication by ell. Its m+1-fold shift is zero, so the
finite geometric sum inverts one minus shift and its Roos limit is zero. The constant
right tower has limit C_m, by diagonal inclusion and the finite-partial-sum splitting
of its difference map. Perfect-reduction/Roos comparison distributes the two-term
free resolution across exact countable products and its cone, with the specified
projection equations. Finite-tail invariance retains the original projection, so
the isomorphism is precisely the evaluated counit of L.adjunction. Internalization
through the exact section equivalence preserves this identification.
For completeness, the original strict quotient rows, before any K-flat replacement,
are killed by ell^(n+1)=u^(n+1)*pi^(e*(n+1)). The ringed power-torsion theorem with
pi and exponents e*(n+1) gives the actual pi-completion unit of their total limit.
Its signed double-Roos and tensor-unit equations identify it with native completion.
The common cohomological bounds give [a,b+1] through the Roos triangle. Choose an
ell-power quotient surjecting onto O_E/pi. The finite counit isomorphism, scalar
associativity and finite scalar preservation of constructibility and Tor bounds
identify the first pi reduction as bounded constructible. Use the normalized
continuous finite-ring comparison to express this in AdicCompletion's internal
quotient category. Keep the equality with the native limit when comparing the two
continuous integer-ring presentations. The empty scheme and zero tower give zero;
the first positive exponent is n=0 and no unramifiedness assumption is used. -/
theorem limit_residue_and_counit [IsNoetherian T]
    (L : Limit l E T D R) (C : spDerivedCoefficientTowers l E T D)
    (hC : spNormalizedConstructibleTorTowers l E T D C) :
    CriterionCondition l E T ((lim l E T D R L).obj C) ∧
      ∀ n : ℕ, IsIso ((spDerivedCoefficientEvaluation l E T D n).map
        ((redLimitAdjunction l E T D R L).counit.app C)) := by
  obtain ⟨hcomplete, hcounit⟩ := normalized_limit_effectivity l E T D R L C hC.2
  have heval (n : ℕ) : IsIso ((spDerivedCoefficientEvaluation l E T D n).map
      ((redLimitAdjunction l E T D R L).counit.app C)) :=
    evaluated_counit_isIso l E T D R L C hcounit n
  obtain ⟨K', hK', hcomplete⟩ := hcomplete
  refine ⟨⟨K', hK', hcomplete, ?_⟩, heval⟩
  exact residue_of_constructible_reductions l E T D R
    ((lim l E T D R L).obj C) K' hK' C hC.1
    ((redLimitAdjunction l E T D R L).counit.app C) heval

end AlgebraicGeometry.ProEtale.NativeTower
