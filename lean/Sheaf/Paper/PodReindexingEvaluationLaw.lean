/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PodReindexingCoherenceData

/-! # Evaluation law for a normalized reindexing comparison

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0GMX, 0A8X, 08J9.
(blueprint: lem-pod-reindexing-evaluation-law).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
Every normalized comparison satisfies the evaluation equation.  This is the
representative evaluation step, with the comparison itself supplied as input.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0GMX, 0A8X and 08J9
(blueprint: lem-pod-reindexing-evaluation-law).

Proof: choose flat-term K-flat and K-injective representatives.  The chain
transpose identifies evaluation on a pure tensor with application of the Hom
map.  The `chain_projection` and `tensorChain_pure` equations identify the two
reindexed maps on every pure generator.  Extensionality after sheafification,
then localization and naturality along resolutions, gives the displayed law for
all derived objects.
-/
theorem comparison_evaluation_law {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt]
    (s : Option ℕ) (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    ∀ M N : podReindexingDerived l E Y s,
      c.tensor.hom.app ((podReindexingDerivedHom l E Y s).obj (op M, N), M) ≫
          SX.tensor.map (Prod.mkHom (c.derived.hom.app (op M, N))
            (𝟙 ((podReindexingDerivedFunctor l E g s).obj M))) ≫
          SX.evaluation ((podReindexingDerivedFunctor l E g s).obj M)
            ((podReindexingDerivedFunctor l E g s).obj N) =
        (podReindexingDerivedFunctor l E g s).map (SY.evaluation M N) := by
  sorry

end WeilConjectures.PodReindexingCoherence
