/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity

/-! # Open reduction as the normalized adjunction mate

## References

* [Stacks, Tag 0GL1]
* [Stacks, Tag 0E8I]
* [Stacks, Tag 07A7]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical open mate is invertible on complete constructible inputs, and its
output has invertible reconstruction unit. -/
theorem integralOpenMateNormalization (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (hX : IsUnit (l : Γ(X, ⊤))) (hY : IsUnit (l : Γ(Y, ⊤)))
    (K : Integral l E X) (hK : sfIntegralConstructible l E X K)
    (hg : Good l E X ((calculus l E X).reduction.obj K))
    (hj : Good l E Y ((Operations.shriek l E o j).obj
      ((calculus l E X).reduction.obj K))) :
    IsIso ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K)) ∧
      IsIso ((m.openReduction l E j).app K) := by
  have _domain := And.intro hX (And.intro hY hj)
  have htor : finiteTorConstructibleIntegral l E X K := by
    obtain ⟨a, b, c, d, _hab, hcd, hb⟩ := hg.2.1
    refine ⟨hK, c, d, hcd, ?_⟩
    intro n
    obtain ⟨hcd', ht⟩ := (hb n).2.2
    refine ⟨hcd', ?_⟩
    intro L P hL f hf hP M i hi
    obtain ⟨e⟩ := hL
    exact ht L P ⟨e ≪≫ ((calculus l E X).reductionEvaluation n).symm.app K⟩
      f hf hP M i hi
  exact (GeneratorReduction.openReconstructionEffectivity l E o m j K (Or.inl htor)).symm

end WeilConjectures.IntegralSystemRealization
