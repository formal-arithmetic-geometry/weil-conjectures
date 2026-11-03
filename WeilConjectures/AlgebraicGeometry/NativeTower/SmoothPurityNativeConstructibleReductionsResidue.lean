/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerIntegralCriterion

/-! # Native residue constructibility from finite reductions

Source: current blueprint sk-lem-sp-tower, second paragraph.
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

/-- Constructible finite ell-power reductions give a bounded constructible first
uniformizer residue. The native and continuous presentations are related by the
specified equality, and the finite comparison maps are supplied explicitly.
No completeness, inverse-limit presentation, or normalization hypothesis is needed.
Source: current blueprint sk-lem-sp-tower.proof.md, second paragraph, and
sk-prop-sp-integral-towers (2); Stacks 099P
(blueprint: lem-sp-native-constructible-reductions-residue).

Proof: retain the heterogeneous equality hK between the native complex K and its
continuous-coefficient presentation K'. Choose a positive
ell-power exponent N whose ideal is contained in (pi), using ell=u*pi^e with e
positive. Evaluation of f identifies the actual N-th derived reduction of K with
the N-th level of C. The normalized coefficient and scalar-extension associativity
comparisons identify the first pi reduction of K' with derived scalar extension of
that finite level from O_E/ell^N to O_E/pi. Over finite coefficient rings this scalar
extension preserves constructibility with the given common Tor interval. Testing
Tor amplitude against the quotient ring itself bounds the cohomology of the result
in that interval. Thus its cohomology is bounded and constructible. The finite
constant/continuous coefficient comparison transports this assertion to the actual
AdicCompletion.derivedReduction of the specified K'. No completion assertion is
needed for this finite scalar calculation. No flatness of O_E/pi over O_E/ell^N, equality
ell=pi, or normalization of C is used. Zero levels and an empty scheme give zero
reductions, for which the same bound and constructibility assertion hold. -/
theorem residue_of_constructible_reductions [IsNoetherian T]
    (K : Integral l E T) (K' : DerivedCategory (AdicCompletion.Modules l E T))
    (hK : HEq K K')
    (C : spDerivedCoefficientTowers l E T D)
    (hC : spConstructibleTorTowers l E T D C)
    (f : (red l E T D R).obj K ⟶ C)
    (hf : ∀ n : ℕ, IsIso ((spDerivedCoefficientEvaluation l E T D n).map f)) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) T
      ((AdicCompletion.derivedReduction l E T 0).obj K') := by
  sorry

end AlgebraicGeometry.ProEtale.NativeTower
