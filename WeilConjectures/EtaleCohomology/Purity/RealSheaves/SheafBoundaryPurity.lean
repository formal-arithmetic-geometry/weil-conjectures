/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import WeilConjectures.WeilSheaf.DirectImageRestriction
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# Boundary semicontinuity of weights on a separated curve

Let `C₀` be a smooth separated geometrically connected curve over `k₀ = 𝔽_q`, `j : U₀ ⟶ C₀` a
dense open immersion and `ℱ` a lisse Weil sheaf on `U₀` with punctual weights at most `β`. Then
`j_* ℱ` has punctual weights at most `β` on all of `C₀`
(`AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage_of_isSeparated`,
`lem-wf-boundary-semicontinuity` and the first assertion of `sk-p-real-semi`).

This reduces to the affine case `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage`
(Step 0 of the blueprint proof): a closed point `s` of `C₀` has an affine open neighbourhood
`X'₀`, again a smooth geometrically connected curve (a nonempty open of the geometrically
irreducible `C₀`), and the stalk of `j_* ℱ` at `s` is that of `j'_* (ℱ|_{U'₀})` for the
restriction `j' : U'₀ = U₀ ∩ X'₀ ⟶ X'₀`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage_of_isPullback`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.upperStar_of_isOpenImmersion`: restriction to an
  open preserves weight bounds.
- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage_of_isSeparated`: boundary
  semicontinuity of weights on a smooth separated geometrically connected curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace FrobeniusModule

variable {K : Type*} [Field K]

/-- If `α` is an eigenvalue of the Frobenius of `M`, then `α⁻¹` is an eigenvalue of the
Frobenius of the dual `M^∨`, the inverse transpose. -/
theorem hasEigenvalue_dual_inv_of_hasEigenvalue {M : FrobeniusModule K} {α : K}
    (hα : M.frobeniusEnd.HasEigenvalue α) : M.dual.frobeniusEnd.HasEigenvalue α⁻¹ := by
  have hF : M.dual.frobeniusEnd.charpoly = M.frobenius.symm.toLinearMap.charpoly :=
    LinearMap.charpoly_dualMap _
  have hα0 := ne_zero_of_hasEigenvalue hα
  obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
  have h : Module.End.HasEigenvalue (M.frobenius.symm.toLinearMap : Module.End K M.carrier)
      α⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x)
      (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 ?_, hx.2⟩)
    change M.frobenius.symm x = α⁻¹ • x
    calc M.frobenius.symm x = α⁻¹ • (α • M.frobenius.symm x) := (inv_smul_smul₀ hα0 _).symm
      _ = α⁻¹ • x := by
        rw [← map_smul, ← hx.1]
        exact congrArg _ (M.frobenius.symm_apply_apply x)
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hF,
    ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
  exact h

end FrobeniusModule

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

omit [Finite k₀] in
/-- The residue fields of a closed point and of its image under an open immersion have the same
degree over `k₀`. -/
lemma degreeOver_eq_of_isOpenImmersion {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y) [IsOpenImmersion φ]
    [φ.IsOver (Spec (CommRingCat.of k₀))] (z : X) :
    (X ↘ Spec (CommRingCat.of k₀)).degreeOver z =
      (Y ↘ Spec (CommRingCat.of k₀)).degreeOver (φ.base z) := by
  rw [← Scheme.Hom.degreeOver_comp_of_isIso φ (Y ↘ Spec (CommRingCat.of k₀)) z, comp_over φ]

/-- **Restriction to an open preserves weight bounds.** If `F` has weights at most `w`, so has
its pullback along an open immersion `φ`: the stalk of `φ^* F` at a closed point `z` is that of
`F` at `φ z`, a point of the same degree. -/
theorem HasWeightsAtMost.upperStar_of_isOpenImmersion {ι : PadicAlgCl l →+* ℂ} {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))] (φ : X ⟶ Y)
    [IsOpenImmersion φ] [φ.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l Y} {w : ℝ}
    (hF : F.HasWeightsAtMost ι w) : ((upperStar φ).obj F).HasWeightsAtMost ι w := by
  intro z α hα
  have hdeg := degreeOver_eq_of_isOpenImmersion (k₀ := k₀) φ z.1
  obtain ⟨e⟩ := nonempty_equiv_stalk_upperStar φ F z
    ⟨φ.base z.1, Scheme.Hom.map_mem_finitePoints φ z.2⟩ rfl hdeg
  have h := hF _ α (e.hasEigenvalue hα)
  rw [Scheme.Hom.residueCard] at h
  rwa [Scheme.Hom.residueCard, hdeg]

section Semicontinuity

variable {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))]
  {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ C) [IsOpenImmersion j]
  [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
  (ι : PadicAlgCl l →+* ℂ)

/-- A smooth curve `C₀` is locally of finite type over `k₀`. -/
local instance : LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀)) :=
  haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  inferInstance

omit [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
  [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] [IsDominant j] in
/-- Step 0 of `lem-wf-boundary-semicontinuity`, abstractly: if a closed point `x` of `C₀` lies
in the image of an open immersion `i : X'₀ ⟶ C₀` from a smooth geometrically connected affine
curve, then the eigenvalues of the local Frobenius of `j_* ℱ` at `x` satisfy the weight bound,
by the affine case applied to the restriction `j' : U'₀ ⟶ X'₀` of `j`. -/
theorem norm_le_of_hasEigenvalue_stalk_directImage_of_isPullback {X' U' : Scheme.{u}}
    [X'.Over (Spec (CommRingCat.of k₀))] [U'.Over (Spec (CommRingCat.of k₀))] [IsAffine X']
    [SmoothOfRelativeDimension 1 (X' ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X' ↘ Spec (CommRingCat.of k₀))]
    {i : X' ⟶ C} {j' : U' ⟶ X'} {i' : U' ⟶ U}
    [IsOpenImmersion i] [QuasiCompact i] [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [QuasiCompact j'] [j'.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j']
    [IsOpenImmersion i'] [QuasiCompact i'] [i'.IsOver (Spec (CommRingCat.of k₀))]
    (h : IsPullback j' i' i j) {F : WeilSheaf k₀ l U} (hF : F.IsLisse) {β : ℝ}
    (hw : F.HasWeightsAtMost ι β) (y : X'.finitePoints) (x : C.finitePoints)
    (hyx : i.base y.1 = x.1) {α : PadicAlgCl l}
    (hα : (((directImage j).obj F).stalk x).frobeniusEnd.HasEigenvalue α) :
    ‖ι α‖ ≤ ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) ^ (β / 2) := by
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) :=
    haveI := SmoothOfRelativeDimension.smooth 1 (X' ↘ Spec (CommRingCat.of k₀))
    inferInstance
  have hjp : j ≫ C ↘ Spec (CommRingCat.of k₀) = U ↘ Spec (CommRingCat.of k₀) := comp_over j _
  have : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := hjp ▸ inferInstance
  obtain ⟨E⟩ := nonempty_equiv_stalk_directImage_of_isPullback h F y x hyx
  have hF' : ((upperStar i').obj F).IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ hF
  have key := hasWeightsAtMost_directImage j' ι hF' (hw.upperStar_of_isOpenImmersion i') y α
    (E.hasEigenvalue hα)
  rwa [Scheme.Hom.residueCard, degreeOver_eq_of_isOpenImmersion i, hyx,
    ← Scheme.Hom.residueCard] at key

/-- Blueprint `lem-wf-boundary-semicontinuity` (first assertion of `sk-p-real-semi`):
*boundary semicontinuity of weights* on a smooth separated geometrically connected curve.

Let `C₀` be a smooth separated geometrically connected curve over `k₀`, `j : U₀ ⟶ C₀` a dense
quasi-compact open immersion and `ℱ` a lisse Weil sheaf on `U₀` with punctual weights at most
`β`. Then `j_* ℱ` has punctual weights at most `β` on all of `C₀`.

Step 0 of the proof: a closed point `s` has an affine open neighbourhood `X'₀`, a smooth
geometrically connected affine curve, on which `j_* ℱ` is the direct image of `ℱ|_{U₀ ∩ X'₀}`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalk_directImage_of_isPullback`); the affine case
is `AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage`. -/
theorem hasWeightsAtMost_directImage_of_isSeparated {F : WeilSheaf k₀ l U} (hF : F.IsLisse)
    {β : ℝ} (hw : F.HasWeightsAtMost ι β) : ((directImage j).obj F).HasWeightsAtMost ι β := by
  intro s α hα
  -- an affine open neighbourhood `V` of `s` and the preimage `W = j⁻¹ V`
  obtain ⟨V, hV, hsV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top s.1)
  have : QuasiSeparatedSpace C :=
    (quasiSeparated_iff_quasiSeparatedSpace (C ↘ Spec (CommRingCat.of k₀))).1 inferInstance
  have : IsAffine V := hV
  have : Nonempty V := ⟨⟨s.1, hsV⟩⟩
  let : (V : Scheme.{u}).Over (Spec (CommRingCat.of k₀)) := ⟨V.ι ≫ C ↘ Spec (CommRingCat.of k₀)⟩
  have : V.ι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  let : (j ⁻¹ᵁ V : Scheme.{u}).Over (Spec (CommRingCat.of k₀)) :=
    ⟨(j ⁻¹ᵁ V).ι ≫ U ↘ Spec (CommRingCat.of k₀)⟩
  have : (j ⁻¹ᵁ V).ι.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hpb : IsPullback (j ∣_ V) (j ⁻¹ᵁ V).ι V.ι j := isPullback_morphismRestrict j V
  have : (j ∣_ V).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change (j ∣_ V) ≫ V.ι ≫ C ↘ Spec (CommRingCat.of k₀) =
      (j ⁻¹ᵁ V).ι ≫ U ↘ Spec (CommRingCat.of k₀)
    rw [← Category.assoc, hpb.w, Category.assoc, comp_over j]⟩
  have : QuasiCompact (j ∣_ V) := MorphismProperty.of_isPullback hpb.flip ‹_›
  have : QuasiCompact (j ⁻¹ᵁ V).ι := MorphismProperty.of_isPullback hpb inferInstance
  have : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict ‹IsDominant j› V
  -- `V` is a smooth geometrically connected affine curve
  have : SmoothOfRelativeDimension 1 ((V : Scheme.{u}) ↘ Spec (CommRingCat.of k₀)) :=
    (zero_add 1) ▸ (inferInstance :
      SmoothOfRelativeDimension (0 + 1) (V.ι ≫ C ↘ Spec (CommRingCat.of k₀)))
  have : GeometricallyConnected ((V : Scheme.{u}) ↘ Spec (CommRingCat.of k₀)) := by
    have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected
      (C ↘ Spec (CommRingCat.of k₀))
    have := GeometricallyIrreducible.comp_of_isOpenImmersion V.ι (C ↘ Spec (CommRingCat.of k₀))
    exact inferInstanceAs (GeometricallyConnected (V.ι ≫ C ↘ Spec (CommRingCat.of k₀)))
  -- the point `s` of `V`
  have hy : (⟨s.1, hsV⟩ : V) ∈ (V : Scheme.{u}).finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso V.ι _).1 s.2
  exact norm_le_of_hasEigenvalue_stalk_directImage_of_isPullback j ι hpb hF hw ⟨_, hy⟩ s rfl hα

/-- Isomorphisms of Frobenius modules can be inverted. -/
private lemma _root_.FrobeniusModule.Equiv.nonempty_symm'' {K : Type*} [Field K]
    {M N : FrobeniusModule K} (e : M.Equiv N) : Nonempty (N.Equiv M) :=
  ⟨⟨e.toLinearEquiv.symm, fun y ↦ by
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    rw [← e.map_frobenius, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]⟩⟩

/-- Blueprint `cor-wf-unramified-boundary-purity` (second assertion; second assertion of
`sk-p-real-semi`): *purity extends over the boundary for a lisse sheaf*.

Let `C₀` be a smooth separated geometrically connected curve over `k₀`, `j : U₀ ⟶ C₀` a dense
quasi-compact open immersion and `𝒢` a lisse Weil sheaf on `C₀` whose restriction `j^* 𝒢` is
punctually `ι`-pure of weight `w`. Then `𝒢` is punctually `ι`-pure of weight `w` on all of `C₀`.

Since `𝒢` is lisse, `𝒢 ≅ j_* j^* 𝒢`
(`AlgebraicGeometry.WeilSheaf.IsLisse.nonempty_iso_directImage_upperStar`), so boundary
semicontinuity (`AlgebraicGeometry.WeilSheaf.hasWeightsAtMost_directImage_of_isSeparated`)
bounds the weights of `𝒢` above by `w`. The same argument for the dual `𝒢^∨`, whose
restriction has weights at most `-w` since duality inverts the local eigenvalues, bounds the
weights of `𝒢` below by `w`. -/
theorem IsLisse.isPunctuallyPureOfWeight_of_upperStar {G : WeilSheaf k₀ l C} (hG : G.IsLisse)
    {w : ℝ} (hw : ((upperStar j).obj G).IsPunctuallyPureOfWeight ι w) :
    G.IsPunctuallyPureOfWeight ι w := by
  have hj : Dense (Set.range j.base) := j.denseRange
  have hjG : ((upperStar j).obj G).IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ hG
  -- the upper bound, from `𝒢 ≅ j_* j^* 𝒢`
  obtain ⟨e⟩ := hG.nonempty_iso_directImage_upperStar j hj
  have hup := hasWeightsAtMost_directImage_of_isSeparated j ι hjG hw.hasWeightsAtMost
  -- the restriction of the dual has weights at most `-w`
  have hD : (G.dual hG).IsLisse := hG.dual
  have hjD : ((upperStar j).obj (G.dual hG)).IsLisse := ProEtale.IsAdicLisseSheaf.upperStar _ hD
  have hwD : ((upperStar j).obj (G.dual hG)).HasWeightsAtMost ι (-w) := by
    intro z α hα
    let x : C.finitePoints := ⟨j.base z.1, Scheme.Hom.map_mem_finitePoints j z.2⟩
    have hdeg := degreeOver_eq_of_isOpenImmersion (k₀ := k₀) j z.1
    obtain ⟨e₁⟩ := nonempty_equiv_stalk_upperStar j (G.dual hG) z x rfl hdeg
    obtain ⟨e₂⟩ := nonempty_equiv_stalk_dual hG x
    obtain ⟨e₃⟩ := nonempty_equiv_stalk_upperStar j G z x rfl hdeg
    obtain ⟨e₄⟩ := e₃.nonempty_symm''
    have h₁ := FrobeniusModule.hasEigenvalue_inv_of_hasEigenvalue_dual
      (e₂.hasEigenvalue (e₁.hasEigenvalue hα))
    have h₂ := hw z α⁻¹ (e₄.hasEigenvalue h₁)
    rw [map_inv₀, norm_inv] at h₂
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg _), ← h₂, inv_inv]
  obtain ⟨eD⟩ := hD.nonempty_iso_directImage_upperStar j hj
  have hdown := hasWeightsAtMost_directImage_of_isSeparated j ι hjD hwD
  -- both bounds at a closed point `x`
  intro x α hα
  have hle := hup x α ((stalkEquivOfIso e x).hasEigenvalue hα)
  obtain ⟨e₂⟩ := nonempty_equiv_stalk_dual hG x
  obtain ⟨e₅⟩ := e₂.nonempty_symm''
  have hαD : ((G.dual hG).stalk x).frobeniusEnd.HasEigenvalue α⁻¹ :=
    e₅.hasEigenvalue (FrobeniusModule.hasEigenvalue_dual_inv_of_hasEigenvalue hα)
  have hge := hdown x α⁻¹ ((stalkEquivOfIso eD x).hasEigenvalue hαD)
  rw [map_inv₀, norm_inv, neg_div, Real.rpow_neg (Nat.cast_nonneg _)] at hge
  have hpos : 0 < ‖ι α‖ :=
    norm_pos_iff.2 ((map_ne_zero ι).2 (FrobeniusModule.ne_zero_of_hasEigenvalue hα))
  have hq : 0 < ((C ↘ Spec (CommRingCat.of k₀)).residueCard x.1 : ℝ) ^ (w / 2) := by
    refine Real.rpow_pos_of_pos ?_ _
    rw [Scheme.Hom.residueCard]
    exact Nat.cast_pos.2 (pow_pos Nat.card_pos _)
  exact le_antisymm hle ((inv_le_inv₀ hpos hq).1 hge)

end Semicontinuity

end AlgebraicGeometry.WeilSheaf
