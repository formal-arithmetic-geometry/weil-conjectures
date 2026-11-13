/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso

/-! # Reindexing finite projective space and its twisting module

## References

* [Stacks Project, Tags 01NF and 01NE](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- A nonempty finite coordinate type can be replaced by `ULift (Fin (n + 1))`,
compatibly with the structure map and the twisting module (Stacks, Tags 01NF and 01NE). -/
theorem exists_finite_index_iso (β : Type u) [Finite β] [Nonempty β] (S : Scheme.{u}) :
    ∃ (n : ℕ) (e : ℙ(β; S) ≅ ℙ(ULift.{u} (Fin (n + 1)); S)),
      e.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = ℙ(β; S) ↘ S ∧
      Nonempty ((Scheme.Modules.pullback e.hom).obj
        (twist (ULift.{u} (Fin (n + 1))) S 1) ≅ twist β S 1) := by
  classical
  let _ := Fintype.ofFinite β
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card β))
  let γ := ULift.{u} (Fin (n + 1))
  let b : γ ≃ β := Equiv.ulift.trans (Fintype.equivFinOfCardEq hn).symm
  let s := fun j : γ ↦ Scheme.Modules.pullbackSection (𝟙 ℙ(β; S))
    (twistOneSection β S (b j))
  let U := fun j : γ ↦ standardOpen β S (b j)
  let hs := fun j : γ ↦
    isFreeGenerator_pullbackSection_twistOneSection (𝟙 ℙ(β; S)) (b j)
  have hU : ⨆ j, U j = ⊤ := (b.iSup_comp).trans (iSup_standardOpen β S)
  let φ := homOfIsFreeGenerator s U hs (ℙ(β; S) ↘ S) hU
  have : IsIso φ := isIso_homOfIsFreeGenerator_reindex β γ b S
  refine ⟨n, asIso φ, homOfIsFreeGenerator_over s U hs _ hU, ?_⟩
  exact ⟨asIso (twistRestrictHom s U hs (ℙ(β; S) ↘ S) hU) ≪≫
    (Scheme.Modules.pullbackId ℙ(β; S)).app (twist β S 1)⟩

end AlgebraicGeometry.ProjectiveSpace
