/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingComparisonCore
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingEvaluationLaw

/-! # Evaluation-normalized reindexing comparison

We construct a reindexing `Comparison` along an isomorphism whose derived and tensor
comparisons are compatible with evaluation (`evaluated_comparison_exists`).

## Implementation details

The chain comparison reindexes each product factor of the ordinary Hom complex and each
total-tensor summand; it descends to the derived comparisons via K-injective and K-flat
representatives. Evaluation is compared on pure tensors using `chain_projection` and
`tensorChain_pure`, then extended by naturality along resolutions. The construction asserts
neither the shift squares nor the uniqueness and transpose laws.

## References

* Stacks Project, Tag 0GMX
* Stacks Project, Tag 0A8X
* Stacks Project, Tag 08J9
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- There is a normalized reindexing comparison `c` whose derived Hom and tensor comparisons
are compatible with the evaluation maps `SY.evaluation` and `SX.evaluation`. -/
theorem evaluated_comparison_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY) :
    ∃ c : Comparison l E g s SX SY TX TY,
      ∀ M N : podReindexingDerived l E Y s,
        c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
          SX.tensor.map (Prod.mkHom (c.derived.hom.app (op M, N))
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
          SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
            ((podReindexingDerivedFunctor l E g s).obj N) =
          (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N) := by
  obtain ⟨c⟩ := comparison_core_exists l E g s SX SY TX TY
  refine ⟨c, ?_⟩
  exact comparison_evaluation_law l E g s SX SY TX TY c

end WeilConjectures.PodReindexingCoherence
