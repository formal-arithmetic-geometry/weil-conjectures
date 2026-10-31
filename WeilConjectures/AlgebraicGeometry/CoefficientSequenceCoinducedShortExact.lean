/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedComplexes
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedKernel
import WeilConjectures.AlgebraicGeometry.CoefficientSequenceCoinducedDifferenceEpi

/-! # Exactness of the ordinary coinduced sequence

Source: Stacks 0941 and the locally finite sequence resolution.
(blueprint: lem-coef-sequence-coinduced-complex-short-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CoefficientCoinduction

private theorem augmentation_mono
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    Mono (complexAugmentation l E W K) := by
  constructor
  intro M f g h
  have he (n : ℕ) : (complexEvaluation l E W n).map f =
      (complexEvaluation l E W n).map g := by
    have hc := congrArg
      (fun b ↦ CoinducedSequence.components (complexEvaluation l E W)
        (complexRight l E W) (complexAdjunction l E W) b n) h
    simpa only [complexAugmentation, CoinducedSequence.components_augmentation] using hc
  apply HomologicalComplex.hom_ext
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  have hU := congrArg (fun t ↦ (t.f i).val.app (Opposite.op U.unop.2)) (he U.unop.1)
  apply ModuleCat.hom_ext
  ext x
  exact congrArg (fun t ↦ t x) hU

/-- The canonical two-term coinduced sequence is short exact, before localization.
Source: Stacks 0941, expanded by the coinduced resolution in
lem-coef-sequence-derived-evaluation-full.
(blueprint: lem-coef-sequence-coinduced-complex-short-exact).

Proof: use the strict-system equivalence to evaluate in every degree at level m.
Coinduction r_n has zero evaluation at m<n and scalar restriction otherwise.
Consequently the first product evaluates to the finite product of N_n for n≤m,
restricted to the level-m ring, and the second to the finite product of the
restricted N_n for n<m. The augmentation sends x in N_m to its transitions to
all lower levels. Its last coordinate is x, so it is monic. The difference
coordinate indexed by n<m is the transition of the (n+1)-coordinate minus the
n-coordinate. Its kernel consists exactly of the families determined by their
last coordinate, hence is the image of the augmentation. To solve the difference
equations for a prescribed target tuple, set the last source coordinate to zero
and solve successively downward: x_n = transition(x_(n+1)) - y_n. This defines a
linear section at level m and proves that the difference is epi. These statements
hold as sheaf morphisms because the formulas commute with restriction. Evaluation
jointly reflects exactness and mono/epi; degree evaluation then gives short
exactness of the short complex of unbounded complexes. At m=0 the second product
is zero and the augmentation is the identity. The zero and empty-site cases use
the same formulas. No infinite product exactness or coefficient flatness is used. -/
theorem complexSequence_shortExact
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{u})
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (complexSequence l E W K).ShortExact := by
  exact { exact := complexSequence_exact l E W K
          mono_f := augmentation_mono l E W K
          epi_g := complexDifference_epi l E W K }

end WeilConjectures.CoefficientCoinduction
