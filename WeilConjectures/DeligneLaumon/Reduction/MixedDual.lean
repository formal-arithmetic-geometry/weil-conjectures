/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import WeilConjectures.DeligneLaumon.Reduction.MixedLisseOpen
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations
public import WeilConjectures.WeilSheaf.LisseDualExact

/-!
# The dual of a mixed lisse Weil sheaf

Clause 6 of the blueprint proposition `proposition-weights-under-usual-operations`: the dual of
a mixed lisse Weil sheaf is mixed, of the negated weights
(`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsIn.dual`); and when a filtration of a lisse sheaf
has lisse graded pieces, their duals are the graded pieces of the annihilator filtration of the
dual (`AlgebraicGeometry.WeilSheaf.nonempty_cokernel_annihilator_iso_dual`).

## Proof

Dualizing is exact on lisse sheaves (`AlgebraicGeometry.WeilSheaf.exact_dualMap`), so the dual
of a lisse sheaf with a filtration by lisse subsheaves with pure graded pieces is mixed, with
graded pieces the duals of those of the filtration, pure of the negated weights
(`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.dual`). In general, by Noetherian induction
(`AlgebraicGeometry.WeilSheaf.isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable`) it
suffices to treat the restriction to a nonempty open on which the graded pieces of a mixed
filtration are lisse
(`AlgebraicGeometry.WeilSheaf.IsMixed.exists_opens_filtrationClosure_isLissePunctuallyPure`); the
dual commutes with pullback (`AlgebraicGeometry.WeilSheaf.upperStarDualIso`). The weights of the
dual are read off from the stalks, which are the duals of the stalks
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_dual`), and a mixed sheaf is mixed with weights
in any set containing its punctual weights (`AlgebraicGeometry.WeilSheaf.isMixedOfWeightsIn_iff`).

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
  {ι : PadicAlgCl l →+* ℂ} {F : WeilSheaf k₀ l X} {S : Set ℝ}

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The punctual weights of the dual of a lisse sheaf are the negatives of those of the sheaf:
the local Frobenius of `F^∨` is the inverse transpose of that of `F`. -/
theorem HasWeightsIn.dual (hF : F.IsLisse) (h : F.HasWeightsIn ι S) :
    (F.dual hF).HasWeightsIn ι (-S) := fun x α hα ↦ by
  obtain ⟨e⟩ := nonempty_equiv_stalk_dual hF x
  obtain ⟨v, hv, hα'⟩ :=
    h x α⁻¹ (FrobeniusModule.hasEigenvalue_inv_of_hasEigenvalue_dual (e.hasEigenvalue hα))
  refine ⟨-v, Set.neg_mem_neg.2 hv, ?_⟩
  rw [map_inv₀, norm_inv, inv_eq_iff_eq_inv] at hα'
  rw [hα', neg_div, Real.rpow_neg (Nat.cast_nonneg _)]

/-- The dual of a lisse sheaf with a finite filtration by lisse subsheaves with punctually pure
graded pieces is mixed: dualizing is exact on lisse sheaves, and the graded pieces of the dual
filtration are the duals of the graded pieces, punctually pure. -/
theorem IsMixed.dual_of_filtrationClosure_isLissePunctuallyPure
    (h : (isLissePunctuallyPure ι).filtrationClosure F) (hF : F.IsLisse) :
    (F.dual hF).IsMixed ι := by
  induction h with
  | of_isZero hX =>
    exact (((isPunctuallyPureOfWeight_of_isZero hX 0).dual hF).isMixedOfWeightsIn
      (Set.mem_univ _)).isMixed
  | @of_mono G' G i _ hX hi ih =>
    have hG' : G'.IsLisse := IsLisse.of_filtrationClosure_isLissePunctuallyPure hX
    obtain ⟨hQ, v, hv⟩ := hi
    obtain ⟨w₁, h₁⟩ := ((hv.dual hQ).isMixedOfWeightsIn (Set.mem_univ _)).isMixed
    obtain ⟨w₃, h₃⟩ := ih hG'
    exact ⟨max w₁ w₃, IsMixedOfWeightsAtMost.of_exact
      (exact_dualMap (ShortComplex.exact_cokernel i) hG' hF hQ)
      (h₁.mono_weight (le_max_left _ _)) (h₃.mono_weight (le_max_right _ _))⟩

/-- **The dual of a mixed lisse sheaf is mixed** (blueprint:
`proposition-weights-under-usual-operations--6`, first assertion, without the weights). -/
theorem IsMixed.dual [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse)
    (h : F.IsMixed ι) : (F.dual hF).IsMixed ι := by
  refine isMixed_of_forall_exists_isMixed_upperStar_opensι_of_stable
    (fun T _ _ H ↦ ∃ (G : WeilSheaf k₀ l T) (hG : G.IsLisse), G.IsMixed ι ∧
      Nonempty (H ≅ G.dual hG)) ?_ ?_ ⟨F, hF, h, ⟨Iso.refl _⟩⟩
  · rintro T T' _ _ _ _ i _ _ H ⟨G, hG, hmix, ⟨e⟩⟩
    exact ⟨_, hG.upperStar i, hmix.upperStar i,
      ⟨(WeilSheaf.upperStar i).mapIso e ≪≫ (upperStarDualIso i G hG).symm⟩⟩
  · rintro T _ _ _ _ _ H ⟨G, hG, hmix, ⟨e⟩⟩
    obtain ⟨U, hU, hUG⟩ := hmix.exists_opens_filtrationClosure_isLissePunctuallyPure
    exact ⟨U, hU, (IsMixed.dual_of_filtrationClosure_isLissePunctuallyPure (hUG U le_rfl)
      (hG.upperStar U.ι)).of_iso
        ((upperStarDualIso U.ι G hG) ≪≫ (WeilSheaf.upperStar U.ι).mapIso e.symm)⟩

/-- **The dual of a mixed lisse sheaf is mixed, of the negated weights.** If a lisse Weil sheaf
`F` on a quasi-compact `k₀`-scheme locally of finite type is `ι`-mixed with weights in `S`, its
dual `F^∨` is `ι`-mixed with weights in `-S`
(blueprint: `proposition-weights-under-usual-operations--6`, first assertion). -/
theorem IsMixedOfWeightsIn.dual [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (hF : F.IsLisse) (h : F.IsMixedOfWeightsIn ι S) : (F.dual hF).IsMixedOfWeightsIn ι (-S) :=
  isMixedOfWeightsIn_iff.2 ⟨h.isMixed.dual hF, h.hasWeightsIn.dual hF⟩

/-- The dual of a lisse sheaf mixed with weights at least `a` is mixed of weights at most `-a`
(blueprint: `proposition-weights-under-usual-operations--6`). -/
theorem IsMixedOfWeightsIn.isMixedOfWeightsAtMost_dual
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (hF : F.IsLisse) {a : ℝ}
    (h : F.IsMixedOfWeightsIn ι (Set.Ici a)) : (F.dual hF).IsMixedOfWeightsAtMost ι (-a) := by
  rw [← isMixedOfWeightsIn_Iic_iff, ← Set.neg_Ici]
  exact h.dual hF

/-- **Graded pieces of the annihilator filtration.** Let `G₁ ⊆ G₂ ⊆ F` be lisse Weil sheaves,
with lisse quotient `G₂ / G₁`, and let `d₁ : F^∨ ⟶ G₁^∨` be the restriction
`F^∨ ⟶ G₂^∨ ⟶ G₁^∨`. The annihilator `G₂^⊥ = ker (F^∨ ⟶ G₂^∨)` is contained in the annihilator
`G₁^⊥ = ker d₁`, with quotient the dual `(G₂ / G₁)^∨`. -/
theorem nonempty_cokernel_annihilator_iso_dual_of_comp_eq {F G₁ G₂ : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (hG₁ : G₁.IsLisse) (hG₂ : G₂.IsLisse) (i₂ : G₂ ⟶ F) [Mono i₂]
    (j : G₁ ⟶ G₂) [Mono j] (hQ : (cokernel j).IsLisse) (d₁ : F.dual hF ⟶ G₁.dual hG₁)
    (hd₁ : dualMap i₂ hG₂ hF ≫ dualMap j hG₁ hG₂ = d₁) :
    Nonempty (cokernel (kernel.lift d₁ (kernel.ι (dualMap i₂ hG₂ hF))
      (by rw [← hd₁, kernel.condition_assoc, zero_comp])) ≅ (cokernel j).dual hQ) := by
  subst hd₁
  set f := dualMap i₂ hG₂ hF
  set g := dualMap j hG₁ hG₂
  have : Epi f := epi_dualMap i₂ hG₂ hF
  have hseq := kernelCokernelCompSequence_exact f g
  have h₀ : (ShortComplex.mk (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
      (kernel.map (f ≫ g) g f (𝟙 _) (by simp)) (by
        ext
        simp)).Exact := hseq.exact 0
  have h₁ : (ShortComplex.mk (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
      (kernelCokernelCompSequence.δ f g) (hseq.toIsComplex.zero 1)).Exact := hseq.exact 1
  have : Epi (kernel.map (f ≫ g) g f (𝟙 _) (by simp)) :=
    h₁.epi_f ((isZero_cokernel_of_epi f).eq_of_tgt _ _)
  have hlift : kernel.lift (f ≫ g) (kernel.ι f) (by rw [kernel.condition_assoc, zero_comp]) =
      kernel.map f (f ≫ g) (𝟙 _) g (by simp) := by
    ext
    simp
  rw [hlift]
  have hSE := ShortComplex.ShortExact.mk' h₀ inferInstance inferInstance
  have hD := exact_dualMap (ShortComplex.exact_cokernel j) hG₁ hG₂ hQ
  have := mono_dualMap (cokernel.π j) hG₂ hQ
  exact ⟨IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hSE.gIsCokernel ≪≫
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) hD.fIsKernel⟩

/-- **Graded pieces of the annihilator filtration.** Let `G₁ ⊆ G₂ ⊆ F` be lisse Weil sheaves,
embedded by `i₁ : G₁ ⟶ F` and `i₂ : G₂ ⟶ F`, with lisse graded piece `G₂ / G₁`. The annihilator
`G₂^⊥ = ker (i₂^∨ : F^∨ ⟶ G₂^∨)` of `G₂` in the dual is contained in the annihilator
`G₁^⊥ = ker (i₁^∨)`, and the graded piece `G₁^⊥ / G₂^⊥` of the annihilator filtration is the dual
`(G₂ / G₁)^∨` of the graded piece (blueprint: `proposition-weights-under-usual-operations--6`,
second assertion). -/
theorem nonempty_cokernel_annihilator_iso_dual {F G₁ G₂ : WeilSheaf k₀ l X}
    (hF : F.IsLisse) (hG₁ : G₁.IsLisse) (hG₂ : G₂.IsLisse) (i₁ : G₁ ⟶ F) (i₂ : G₂ ⟶ F) [Mono i₂]
    (j : G₁ ⟶ G₂) [Mono j] (hj : j ≫ i₂ = i₁) (hQ : (cokernel j).IsLisse) :
    Nonempty (cokernel (kernel.lift (dualMap i₁ hG₁ hF) (kernel.ι (dualMap i₂ hG₂ hF))
      (by rw [← hj, dualMap_comp j i₂ hG₁ hG₂ hF, kernel.condition_assoc, zero_comp])) ≅
        (cokernel j).dual hQ) :=
  nonempty_cokernel_annihilator_iso_dual_of_comp_eq hF hG₁ hG₂ i₂ j hQ _
    (by rw [← dualMap_comp, hj])

end AlgebraicGeometry.WeilSheaf
