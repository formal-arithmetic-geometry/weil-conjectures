/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.MiddleExtension
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkIso
public import WeilConjectures.WeilSheaf.UpperStarPointwise
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact

/-!
# Purity of real lisse Weil sheaves on curves

Let `C₀` be a smooth geometrically connected curve over a finite field `k₀` and `𝒢₀` an `ι`-real
lisse Weil sheaf on `C₀`. Every irreducible constituent of `𝒢₀` is punctually `ι`-pure, of its
determinant weight. This is the main theorem of the blueprint section `sec-purity-real-sheaves`,
formalised there on the side of representations of the Weil group
(`AlgebraicGeometry.WeilGroup.isPunctuallyPure_of_isConstituent_of_isReal`); this file states
it for Weil sheaves, with irreducible constituents rendered as irreducible lisse subquotients
`𝒢₂ / 𝒢₁` of lisse Weil subsheaves `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel`: blueprint
  `thm-rp-real-lisse-purity-affine` (`sk-p-real-purity`).
- `AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`: blueprint
  `lem-wf-boundary-semicontinuity` (`sk-p-real-semi`).
- `AlgebraicGeometry.WeilSheaf.IsLisse.isPunctuallyPureOfWeight_of_upperStar`: blueprint
  `cor-wf-unramified-boundary-purity`, consequence clause (`sk-p-real-semi`), deduced from
  boundary semicontinuity applied to the sheaf and to its dual.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Purity of real lisse sheaves on curves** (blueprint: `thm-rp-real-lisse-purity-affine`,
`sk-p-real-purity`, of the section `sec-purity-real-sheaves`). Let `C₀` be a smooth geometrically
connected curve over `k₀` and `𝒢₀` an `ι`-real lisse Weil sheaf on `C₀`. Every irreducible
constituent of `𝒢₀`, that is, every irreducible lisse quotient `𝒢₂ / 𝒢₁` of lisse Weil subsheaves
`𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢₀`, is punctually `ι`-pure (of its determinant weight).

This is a weakening of the blueprint node: the weight is only asserted to exist, not to be the
determinant weight `wt_ι(det 𝒢₂/𝒢₁) / rank(𝒢₂/𝒢₁)`. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel {ι : PadicAlgCl l →+* ℂ}
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] {𝒢 : WeilSheaf k₀ l C} (h𝒢 : 𝒢.IsLisse)
    (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l C} (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i]
    [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse) (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w :=
  sorry


/-- *Boundary semicontinuity of weights* on a curve: let `j : U₀ ⟶ C₀` be a dense open immersion
into a smooth geometrically connected curve over `k₀`. If the lisse sheaf `F` on `U₀` has punctual
weights at most `β`, then so has its direct image `j_*F` at every closed point of `C₀`, including
the finitely many points outside `U₀`, where it may be singular.
(blueprint: `lem-wf-boundary-semicontinuity`) -/
theorem IsLisse.hasWeightsAtMost_directImage {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hj : Dense (Set.range j.base)) {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    {ι : PadicAlgCl l →+* ℂ} {β : ℝ} (hβ : F.HasWeightsAtMost ι β) :
    ((directImage j).obj F).HasWeightsAtMost ι β :=
  sorry

/-- *Upper weight bounds extend over the missing points.* Let `G` be a lisse Weil sheaf on a
smooth geometrically connected curve `C` over `k₀` and `j : U ↪ C` a dense open immersion. If
`j^*G` has weights at most `w`, then so has `G ≅ j_* j^* G`, by boundary semicontinuity
(`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_directImage`). -/
theorem IsLisse.hasWeightsAtMost_of_upperStar {ι : PadicAlgCl l →+* ℂ}
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l C} (hG : G.IsLisse) {w : ℝ}
    (hw : ((WeilSheaf.upperStar j).obj G).HasWeightsAtMost ι w) : G.HasWeightsAtMost ι w := by
  obtain ⟨e⟩ := hG.nonempty_iso_directImage_upperStar j j.denseRange
  have h := IsLisse.hasWeightsAtMost_directImage j j.denseRange
    (hG.upperStar j) hw
  intro x
  obtain ⟨E⟩ := nonempty_equiv_stalk_of_iso e x
  exact (h x).of_equiv E

/-- **Purity extends over the missing points.** Let `G` be a lisse Weil sheaf on a smooth
geometrically connected curve `C` over `k₀` and `j : U ↪ C` a dense open immersion such that
`j^*G` is punctually `ι`-pure of weight `w`. Then `G` is punctually `ι`-pure of weight `w` on all
of `C`. By boundary semicontinuity applied to `G ≅ j_* j^* G`
(`AlgebraicGeometry.WeilSheaf.IsLisse.hasWeightsAtMost_of_upperStar`), `G` has weights at most
`w`, and likewise its dual `G^∨`, whose restriction `j^*G^∨` is pure of weight `-w`, has weights
at most `-w`; so the eigenvalues of the local Frobenius of `G` are pure of weight `w`.
(blueprint: `cor-wf-unramified-boundary-purity`, consequence clause, subsection `sk-p-real-semi`)
-/
theorem IsLisse.isPunctuallyPureOfWeight_of_upperStar {ι : PadicAlgCl l →+* ℂ}
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
    [QuasiCompact j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l C} (hG : G.IsLisse) {w : ℝ}
    (hw : ((WeilSheaf.upperStar j).obj G).IsPunctuallyPureOfWeight ι w) :
    G.IsPunctuallyPureOfWeight ι w := by
  have hle := hG.hasWeightsAtMost_of_upperStar j hw.hasWeightsAtMost
  have hdw : ((WeilSheaf.upperStar j).obj (G.dual hG)).IsPunctuallyPureOfWeight ι (-w) := fun z ↦ by
    obtain ⟨E⟩ := nonempty_equiv_stalk_dual hG
      ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩
    exact (isPureOfWeight_stalk_upperStar_iff j _ z).2
      ((((isPureOfWeight_stalk_upperStar_iff j G z).1 (hw z)).dual).of_equiv E)
  have hle' := hG.dual.hasWeightsAtMost_of_upperStar j hdw.hasWeightsAtMost
  intro x
  obtain ⟨E⟩ := nonempty_equiv_stalk_dual hG x
  exact FrobeniusModule.IsPureOfWeight.of_hasWeightsAtMost_of_equiv_dual E (hle x) (hle' x)

end AlgebraicGeometry.WeilSheaf
