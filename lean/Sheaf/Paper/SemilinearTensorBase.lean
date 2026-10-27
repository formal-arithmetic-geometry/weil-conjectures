module

public import Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Base tensor models for semilinear systems
Source: Zheng Construction 4.1 and Stacks 06YS, 07A4.
(blueprint: lem-coef-semilinear-tensor-coherence-base)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
/-- The closed structures and K-flat tensor models used by all comparisons. -/
structure SystemTensorBase where
  closed : Closed.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ)
  tensorModels : Models.{c, v, r} (coefficientSequenceTopology J)
    (systemRing.{c, v, max c v r} J B τ) closed
  levelClosed : ∀ n : ℕ, Closed.{c, v, r} J (B n)
  levelTensorModels : ∀ n : ℕ, Models.{c, v, r} J (B n) (levelClosed n)
/-- Proof: choose the closed structure and K-flat model from the ringed-site
derived tensor construction.
Source: Zheng Construction 4.1; the representative K-flat descent construction. -/
theorem systemTensorBase_nonempty :
    Nonempty (SystemTensorBase.{c, v, r} J B τ) := by
  classical
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : HasSheafify (coefficientSequenceTopology J) AddCommGrpCat.{max c v r} :=
    abelianSheafify (coefficientSequenceTopology J)
  obtain ⟨S, _, T, _⟩ := RingedDerivedNative.closedAdjunction.{c, v, r, (max c v r) + 1}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ)
  have levels (n : ℕ) : ∃ S : Closed.{c, v, r} J (B n),
      Nonempty (Models.{c, v, r} J (B n) S) := by
    obtain ⟨S, _, T, _⟩ := RingedDerivedNative.closedAdjunction.{c, v, r, (max c v r) + 1}
      J (B n)
    exact ⟨S, ⟨T⟩⟩
  choose levelClosed levelModels using levels
  exact ⟨⟨S, T, levelClosed, fun n ↦ Classical.choice (levelModels n)⟩⟩
end WeilConjectures.SemilinearSections
