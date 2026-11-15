/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageZero
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageExtension
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageAssembly

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Every étale hypercover `K` of a qcqs scheme receives a map from a finite split étale
hypercover (Stacks, Tags 0DAV, 094K, 01GS). -/
theorem exists_finite_split_replacement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K) :
    ∃ V : FiniteSplitEtaleHypercover X, Nonempty (V.simplicial ⟶ K) := by
  classical
  obtain ⟨A₀⟩ := exists_replacement_stage_zero K hK
  have hstep (n : ℕ) (A : FiniteSplitReplacementStage K n) :=
    exists_replacement_stage_extension K hK n A
  choose next hnext using hstep
  let A : ∀ n, FiniteSplitReplacementStage K n :=
    Nat.rec A₀ (fun n B ↦ next n B)
  exact exists_replacement_of_stage_tower K A (fun n ↦ hnext n (A n))

end AlgebraicGeometry.FiniteSplitEtaleHypercover
