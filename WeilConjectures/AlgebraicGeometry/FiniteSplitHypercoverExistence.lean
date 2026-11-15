/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverReplacement

/-! Intermediate construction for finite split hypercover refinement. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Every qcqs scheme `X` admits a finite split étale hypercover
(Stacks, Tags 0DAV, 094K, 01GS). -/
theorem exists_finite_split_hypercover (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] : Nonempty (FiniteSplitEtaleHypercover X) := by
  let E : X.Etale := Scheme.Etale.mk (𝟙 X)
  let K : SimplicialObject X.Etale := (Functor.const _).obj E
  have hE : IsTerminal ((Scheme.Etale.forget X).obj E) := Over.mkIdTerminal
  have hK : IsEtaleHypercover K := by
    intro n
    refine ⟨E, (fun _ _ _ ↦ 𝟙 E), 𝟙 E, ?_, ?_, ?_, ?_⟩
    · intros
      simp [K]
    · intro T p hp
      refine ⟨hE.from T, ?_, ?_⟩
      · intro Δ h θ
        exact hE.hom_ext _ _
      · intro f hf
        exact hE.hom_ext _ _
    · intros
      simp [K]
    · change Surjective (𝟙 X)
      infer_instance
  obtain ⟨V, _⟩ := exists_finite_split_replacement K hK
  exact ⟨V⟩

end AlgebraicGeometry.FiniteSplitEtaleHypercover
