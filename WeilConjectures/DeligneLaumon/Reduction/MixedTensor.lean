/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.MixedLisseOpen
public import WeilConjectures.DeligneLaumon.Reduction.MixedStalk
public import WeilConjectures.WeilSheaf.LisseDualExact

/-!
# Tensor products of mixed Weil sheaves

Clause 5 of the blueprint proposition `proposition-weights-under-usual-operations`: the tensor
product of mixed sheaves of weights at most `a` and `b` is mixed of weights at most `a + b`
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.tensorObj`). The tensor product
`F ⊗ G = [F^∨, G]` of Weil sheaves (`AlgebraicGeometry.WeilSheaf.tensorObj`) is only defined
for a lisse first factor `F`.

## Proof

The weights of `F ⊗ G` at a closed point are the sums of those of `F` and `G`
(`AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.tensorObj`), so it suffices to show that `F ⊗ G`
is mixed (`AlgebraicGeometry.WeilSheaf.IsMixed.isMixedOfWeightsAtMost`). By Noetherian induction
(`AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable`), the
tensor product commuting with pullback (`AlgebraicGeometry.WeilSheaf.upperStarTensorObjIso`), it
suffices to show this on a nonempty open on which the graded pieces of a mixed filtration of `F`
are lisse
(`AlgebraicGeometry.WeilSheaf.IsMixed.exists_opens_filtrationClosure_isLissePunctuallyPure`).
There the tensor product is exact in both variables
(`AlgebraicGeometry.WeilSheaf.exact_tensorHom_id`, `AlgebraicGeometry.WeilSheaf.tensorLeft`),
and the tensor products of the graded pieces are punctually pure
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.tensorObj`).

The Noetherian induction needs the base `X` to be quasi-compact: mixedness is the existence of a
global finite filtration.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  {ι : PadicAlgCl l →+* ℂ} {F G : WeilSheaf k₀ l X}

/-- The tensor product of a lisse sheaf with a finite filtration by lisse subsheaves with
punctually pure graded pieces and of a mixed sheaf is mixed: the tensor product is exact in both
variables, and the tensor products of punctually pure sheaves are punctually pure. -/
theorem IsMixed.tensorObj_of_filtrationClosure_isLissePunctuallyPure
    (h : (isLissePunctuallyPure ι).filtrationClosure F) (hF : F.IsLisse) (hG : G.IsMixed ι) :
    (F.tensorObj G hF).IsMixed ι := by
  induction h with
  | @of_isZero F hX =>
    have hpure : (F.tensorObj G hF).IsPunctuallyPureOfWeight ι 0 := fun x μ hμ ↦ by
      obtain ⟨a, -, ha, -, -⟩ := exists_of_hasEigenvalue_stalk_tensorObj hF hμ
      exact (not_hasEigenvalue_stalk_of_isZero hX x a ha).elim
    exact (hpure.isMixedOfWeightsIn (Set.mem_univ _)).isMixed
  | @of_mono F' F i _ hX hi ih =>
    have hF' : F'.IsLisse := IsLisse.of_filtrationClosure_isLissePunctuallyPure hX
    obtain ⟨hQ, v, hv⟩ := hi
    obtain ⟨w, hw⟩ := hG
    obtain ⟨w₁, h₁⟩ := ih hF'
    have h₃ := hw.map_add (tensorLeft (cokernel i) hQ) v fun v' G' hG' ↦ by
      rw [add_comm]
      exact hv.tensorObj hQ hG'
    exact ⟨max w₁ (w + v), IsMixedOfWeightsAtMost.of_exact
      (exact_tensorHom_id (ShortComplex.exact_cokernel i) hF' hF hQ G)
      (h₁.mono_weight (le_max_left _ _)) (h₃.mono_weight (le_max_right _ _))⟩

/-- **The tensor product of mixed sheaves is mixed** (blueprint:
`proposition-weights-under-usual-operations--5`, without the weights). The
scheme `X` is assumed quasi-compact over `k₀`, unlike in the blueprint: mixedness is a global
filtration, built here by Noetherian induction. -/
theorem IsMixed.tensorObj [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse)
    (hFm : F.IsMixed ι) (hG : G.IsMixed ι) : (F.tensorObj G hF).IsMixed ι := by
  refine isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable
    (fun T _ _ H ↦ ∃ (F G : WeilSheaf k₀ l T) (hF : F.IsLisse), F.IsMixed ι ∧ G.IsMixed ι ∧
      Nonempty (H ≅ F.tensorObj G hF)) ?_ ?_ ⟨F, G, hF, hFm, hG, ⟨Iso.refl _⟩⟩
  · rintro T T' _ _ _ _ i _ _ H ⟨F, G, hF, hFm, hG, ⟨e⟩⟩
    exact ⟨_, _, hF.upperStar i, hFm.upperStar i, hG.upperStar i,
      ⟨(WeilSheaf.upperStar i).mapIso e ≪≫ upperStarTensorObjIso i F G hF⟩⟩
  · rintro T _ _ _ _ _ H ⟨F, G, hF, hFm, hG, ⟨e⟩⟩
    obtain ⟨U, hU, hUF⟩ := hFm.exists_opens_filtrationClosure_isLissePunctuallyPure
    exact ⟨U, hU, (IsMixed.tensorObj_of_filtrationClosure_isLissePunctuallyPure (hUF U le_rfl)
      (hF.upperStar U.ι) (hG.upperStar U.ι)).of_iso
        ((upperStarTensorObjIso U.ι F G hF).symm ≪≫ (WeilSheaf.upperStar U.ι).mapIso e.symm)⟩

/-- **Tensor products of mixed sheaves.** On a quasi-compact `k₀`-scheme locally of finite type,
the tensor product `F ⊗ G` of a lisse Weil sheaf `F` mixed of weights at most `a` and a Weil
sheaf `G` mixed of weights at most `b` is mixed of weights at most `a + b`
(blueprint: `proposition-weights-under-usual-operations--5`). -/
theorem IsMixedOfWeightsAtMost.tensorObj [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (hF : F.IsLisse) {a b : ℝ} (hFa : F.IsMixedOfWeightsAtMost ι a)
    (hGb : G.IsMixedOfWeightsAtMost ι b) : (F.tensorObj G hF).IsMixedOfWeightsAtMost ι (a + b) :=
  (hFa.isMixed.tensorObj hF hGb.isMixed).isMixedOfWeightsAtMost
    (HasWeightsAtMost.tensorObj hF hFa.hasWeightsAtMost hGb.hasWeightsAtMost)

end AlgebraicGeometry.WeilSheaf
