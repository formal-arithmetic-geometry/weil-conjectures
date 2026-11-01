/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparison

/-! # One finite evaluation of the intrinsic refinement

Source: Stacks 0F7B and the finite-evaluation argument in Step 1 of
lem-pur-reconstructed-pair-refinement-coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures CompactSupportCondensedRealization PurIntegralSupportComparison

namespace WeilConjectures.ReconstructedPairRefinement

/-- A single finite evaluation of the actual system refinement is invertible on
bounded-below etale-origin inputs. Only this level needs an origin witness.
Source: Stacks 0F7B; parent node Step 1
(blueprint: lem-pur-refinement-finite-origin-evaluation).

Proof: evaluate the open-adjunction construction and proper compositor using the
simultaneous semilinear-section comparison. The coordinate equivalence restricts
scalars along the canonical quotient-ring isomorphism and hence retains the
underlying sections and normalized adjunction units. Transport the supplied etale
origin through this quotient isomorphism. At this positive finite coefficient level,
the constant-ring proper/open mate is invertible by the finite-torsion proper/open
calculus, using the given lower bound of the etale origin. The evaluated proper
compositor and the identity-edge comparisons are isomorphisms. Conjugating the
constant-ring mate by these comparisons proves the claim. This calculation needs
no origin at another level, no normalization and no global lower bound. It does
not infer equality of derived maps from their evaluations. -/
theorem systemRefinementEvaluation_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (X Y : CondensedERealization.Base k) (f : X.scheme ⟶ Y.scheme)
    [f.IsOver (Spec (.of k))] {c d : Compactification f} (w : c.Refinement d)
    (P : StrictEtaleEvaluation X.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E))
    (V : BrownTowerComparison.Site X.scheme (integralExceptionalIntegers l E)
      (integralExceptionalUniformizer l E) P)
    (M : coefficientSequenceDerived.{u, u} l E X.scheme) (n : ℕ)
    (_hM : ∃ H : DerivedCategory (strictEtaleLevel X.scheme
      (integralExceptionalIntegers l E) (integralExceptionalUniformizer l E) n),
      (∃ a : ℤ, H.IsGE a) ∧
        Nonempty ((V.comparison.evaluation.level n).inverse.obj H ≅
          (V.proEvaluation.evaluation n).obj ((coordinates l E X.scheme).functor.obj M))) :
    IsIso ((coefficientSequenceDerivedEvaluation l E Y.scheme n).map
      ((systemRefinement l E k X Y f w).app M)) := by
  sorry

end WeilConjectures.ReconstructedPairRefinement
