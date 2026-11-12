/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.RealSheaves

/-!
# Noetherian induction for mixedness

Let `P` be a property of Weil sheaves on `k₀`-schemes locally of finite type which is stable
under pullback along closed immersions. If on every nonempty reduced quasi-compact `T` every
sheaf with `P` is mixed on a nonempty open of `T`, then every sheaf with `P` on a quasi-compact
`k₀`-scheme `X` locally of finite type is mixed
(`AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable`).

This is the Noetherian induction of `thm-zl-real-mixed-by-curves`
(`AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι`, specialised
there to real sheaves on separated schemes), for an arbitrary property: on a reduced closed
subscheme `T` of `X`, a sheaf with `P` is mixed on a nonempty open `U` by hypothesis and, by
induction, on the reduced closed complement of `U`; mixed filtrations glue along the open–closed
exact sequence (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

/- Through `Mathlib.AlgebraicGeometry.Group.Affine`, `Spec k₀` is also an object over itself via
`specOverSpec`; prefer the identity structure `CategoryTheory.instOverClass`. -/
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- **Noetherian induction for mixedness.** Let `P` be a property of Weil sheaves on
`k₀`-schemes locally of finite type, stable under pullback along closed immersions over `k₀`.
Suppose that on every nonempty reduced quasi-compact `k₀`-scheme `T` locally of finite type,
every Weil sheaf with `P` is `ι`-mixed on some nonempty open of `T`. Then every Weil sheaf with
`P` on a quasi-compact `k₀`-scheme locally of finite type is `ι`-mixed
(blueprint: `thm-zl-real-mixed-by-curves`, the Noetherian induction; used in
`proposition-weights-under-usual-operations`). -/
theorem isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable
    (P : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))], WeilSheaf k₀ l T → Prop)
    (hP : ∀ (T T' : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] [T'.Over (Spec (CommRingCat.of k₀))]
      [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))] (i : T' ⟶ T) [IsClosedImmersion i]
      [i.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T), P T G →
        P T' ((WeilSheaf.upperStar i).obj G))
    (h : ∀ (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))] [IsReduced T] [Nonempty T]
      [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
      [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l T), P T G →
        ∃ U : T.Opens, (U : Set T).Nonempty ∧ ((WeilSheaf.upperStar U.ι).obj G).IsMixed ι)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : P X F) :
    F.IsMixed ι := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))
  -- Noetherian induction on the closed subsets of `X`.
  have key : ∀ (Z : Closeds X) (T : Scheme.{u}) [T.Over (Spec (CommRingCat.of k₀))]
      [IsReduced T] (i : T ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))],
      Set.range i ⊆ Z → ∀ G : WeilSheaf k₀ l T,
        haveI : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
          rw [← comp_over i]
          infer_instance
        P T G → G.IsMixed ι := by
    intro Z
    induction Z using WellFoundedLT.induction with
    | ind Z ih =>
    intro T _ _ i _ _ hiZ G hG
    have : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]
      infer_instance
    have : QuasiCompact (T ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over i]
      infer_instance
    have := isNoetherian_of_locallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))
    cases isEmpty_or_nonempty T
    · exact ⟨0, isMixedOfWeightsAtMost_of_isEmpty G 0⟩
    obtain ⟨U, ⟨u, hu⟩, w₁, hU⟩ := h T G hG
    -- The reduced closed complement `T'` of `U`.
    let C : Closeds T := ⟨(U : Set T)ᶜ, U.isOpen.isClosed_compl⟩
    let i' := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
    let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over
        (Spec (CommRingCat.of k₀)) := ⟨i' ≫ T ↘ Spec (CommRingCat.of k₀)⟩
    have : i'.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
    have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal C).subscheme ↘
        Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i' ≫ _))
    have hrange : Set.range i' = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let Z' : Closeds X := ⟨i '' C, i.isClosedEmbedding.isClosedMap _ C.isClosed⟩
    have hZ' : Z' < Z := by
      refine lt_of_le_of_ne (fun y ⟨t, _, ht⟩ ↦ hiZ ⟨t, ht⟩) fun h ↦ ?_
      have : i u ∈ (Z' : Set X) := h ▸ hiZ ⟨u, rfl⟩
      obtain ⟨t, ht, hti⟩ := this
      exact ht (i.isClosedEmbedding.injective hti ▸ hu)
    obtain ⟨w₂, hT'⟩ := ih Z' hZ' _ (i' ≫ i) (by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange]
      exact subset_rfl)
      _ (hP _ _ i' G hG)
    have : NoetherianSpace U.toScheme := inferInstanceAs (NoetherianSpace (U : Set T))
    exact ⟨max w₁ w₂, IsMixedOfWeightsAtMost.of_openClosed (j := U.ι) (i := i')
      (by
        rw [Scheme.Opens.range_ι, hrange]
        exact isCompl_compl)
      (hU.mono_weight (le_max_left _ _)) (hT'.mono_weight (le_max_right _ _))⟩
  -- `X` is the union of the empty open and its reduction.
  let i := (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme.Over
      (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType ((Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)).subscheme ↘
      Spec (CommRingCat.of k₀)) := inferInstanceAs (LocallyOfFiniteType (i ≫ _))
  have : IsEmpty (⊥ : X.Opens).toScheme := ⟨fun x ↦ x.2⟩
  have : QuasiCompact (⊥ : X.Opens).ι := inferInstance
  obtain ⟨w, hw⟩ := key ⊤ _ i (Set.subset_univ _) _ (hP _ _ i F hF)
  exact ⟨w, IsMixedOfWeightsAtMost.of_openClosed (j := (⊥ : X.Opens).ι) (i := i)
    (by
      rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact isCompl_bot_top)
    (isMixedOfWeightsAtMost_of_isEmpty _ w) hw⟩

end AlgebraicGeometry.WeilSheaf
