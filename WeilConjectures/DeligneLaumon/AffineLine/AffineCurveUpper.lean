/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Fiber
public import WeilConjectures.DeligneLaumon.AffineLine.Purity
public import WeilConjectures.DeligneLaumon.AffineLine.LocalDuality
public import WeilConjectures.DeligneLaumon.AffineLine.Upper
public import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension
public import WeilConjectures.WeilSheaf.FiniteEtaleLisse
public import WeilConjectures.WeilSheaf.Curve
public import WeilConjectures.WeilSheaf.LowerStarId
public import WeilConjectures.WeilSheaf.UpperStarPointwise

/-!
# The compact-support upper bound on affine curves

Let `C₀` be a smooth geometrically connected affine curve over `k₀ = 𝔽_q` and `𝓕` a lisse Weil
sheaf on `C₀`, punctually `ι`-pure of weight `w`. Then `H_c^i(C, 𝓕)` has weights at most `w + i`
(blueprint: `thm-a1-affine-curve-upper`).

The degree-one bound is reduced to the Deligne–Laumon estimate on the affine line for a sheaf
unramified at infinity (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one`):

* the boundary sequence of `j : U₀ ↪ 𝔸¹` passes from `H_c^1(𝔸¹, j_*𝓔)` to `H_c^1(U, 𝓔)`, the
  boundary contributing weights at most `w`;
* finitely many points may be removed from the curve: `H_c^1` of the smaller open surjects onto
  `H_c^1` of the larger one.

## Main statements

- `AlgebraicGeometry.WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite`:
  blueprint `lem-a1-finite-boundary-weights`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf`:
  the degree-one bound on `U₀` for a sheaf unramified at infinity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilSheaf

/-- **Weights of the cohomology of a finite boundary.** Let `Z` be finite over `k₀` and `𝓖` a
Weil sheaf on `Z` whose stalks have weights at most `w`. Then `H_c^0(Z, 𝓖)` has weights at most
`w`. (blueprint: `lem-a1-finite-boundary-weights`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [IsFinite (Z ↘ Spec (CommRingCat.of k₀))]
    {ι : PadicAlgCl l →+* ℂ} {G : WeilSheaf k₀ l Z} {w : ℝ} (hG : G.HasWeightsAtMost ι w) :
    (G.compactlySupportedCohomology 0).HasWeightsAtMostOver k₀ ι w := by
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    (Z ↘ Spec (CommRingCat.of k₀)) G 0
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E.symm
    (WeilSheaf.HasWeightsAtMost.higherLowerShriek_zero_of_quasiFinite _ hG).compactlySupportedCohomology_zero

end WeilSheaf

namespace WeilSheaf.LisseOnDenseOpen

/-- The complement of the dense open `U₀` in the affine line is finite. -/
theorem finite_compl_range (D : LisseOnDenseOpen k₀ l) :
    ((Set.range D.j.base)ᶜ).Finite := by
  have hd : Dense (D.j.opensRange : Set (affineLine k₀)) := D.isDominant.denseRange
  obtain ⟨b, ⟨s, hs⟩, hb⟩ :=
    AffineSpace.exists_basicOpen_forall_exists_mem_and_finite D.j.opensRange hd.nonempty
  exact (hb s hs).2.subset fun x hx ↦ ⟨hx, Subsingleton.elim _ _⟩

variable (ι : PadicAlgCl l →+* ℂ)

/-- **Degree one on the open, unramified at infinity.** Let `𝓔` be lisse on the dense open
`U₀ ⊆ 𝔸¹`, punctually `ι`-pure of weight `w` and unramified at infinity. Then `H_c^1(U, 𝓔)` has
weights at most `w + 1`: the boundary sequence
`H_c^0(Z, i^*j_*𝓔) → H_c^1(U, 𝓔) → H_c^1(𝔸¹, j_*𝓔)` of `j`, the affine-line estimate for the
middle extension, and the boundary semicontinuity of weights. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf (D : LisseOnDenseOpen k₀ l)
    (hinf : D.IsUnramifiedAtInfinity) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.sheaf.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  obtain ⟨Z, _, i, _, _, hrange, _⟩ :=
    Scheme.Opens.exists_isClosedImmersion_isFinite_compl (k₀ := k₀) D.j.opensRange
      (by simpa [Scheme.Hom.coe_opensRange] using D.finite_compl_range)
  have hij : Set.range i.base = (Set.range D.j.base)ᶜ := by
    rw [hrange, Scheme.Hom.coe_opensRange]
  obtain ⟨⟨δ, g, hex, -, hδ, hg⟩, -⟩ :=
    exists_exact_compactlySupportedCohomology_boundary D.j i hij D.sheaf D.lisse
  -- the middle extension on the line: the affine-line estimate
  have hA := D.hasWeightsAtMostOver_compactlySupportedCohomology_one ι hinf hw
  rw [directImage_eq] at hA
  -- the boundary: weights at most `w`
  have hd := D.hasWeightsAtMost_directImage hw.hasWeightsAtMost
  rw [directImage_eq] at hd
  have hB := WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_zero_of_isFinite
    (hd.upperStar i)
  exact FrobeniusModule.HasWeightsAtMost.of_functionExact δ g hδ hg hex
    (hB.mono Nat.card_pos (by linarith)) hA

end WeilSheaf.LisseOnDenseOpen

namespace WeilSheaf

variable (ι : PadicAlgCl l →+* ℂ)

/-- **Degree one on an open of the line, unramified at infinity**, for an unbundled open immersion
`j : U₀ ↪ 𝔸¹`: if `𝓔` is lisse on `U₀`, punctually `ι`-pure of weight `w` and unramified at
infinity, then `H_c^1(U, 𝓔)` has weights at most `w + 1`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    {E : WeilSheaf k₀ l U} (hE : E.IsLisse) (hinf : E.IsUnramifiedAtInfinity j) {w : ℝ}
    (hw : E.IsPunctuallyPureOfWeight ι w) :
    (E.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) :=
  LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology_one_sheaf ι
    ⟨U, j, E, hE⟩ hinf hw

variable {ι}

/-- **Degree one on an open of `ℙ¹` containing `∞`.** Let `W ⊆ ℙ¹` be an open containing the
point at infinity and `𝓖` a lisse Weil sheaf on `W`, punctually `ι`-pure of weight `w`. Then
`H_c^1(W, 𝓖)` has weights at most `w + 1`: it is a quotient of `H_c^1(V, 𝓖|_V)` for the part
`V = W ∩ 𝔸¹` of `W` in the affine chart, whose complement in `W` is at most the point `∞`, and
`𝓖|_V` is unramified at infinity, since it extends to the lisse sheaf `𝓖` on `W ∋ ∞`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_opens_projectiveLine
    (W : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens)
    [IsSeparated (W.toScheme ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (W.toScheme ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (W.toScheme ↘ Spec (CommRingCat.of k₀))]
    (hWtop : (ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))).opensRange ⊔ W = ⊤)
    {G : WeilSheaf k₀ l W} (hG : G.IsLisse) {w : ℝ} (hw : G.IsPunctuallyPureOfWeight ι w) :
    (G.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  let a := ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))
  have := isNoetherian_of_locallyOfFiniteType
    (ProjectiveLine (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  -- the part `V` of `W` in the affine chart; its complement in `W` lies over `∞`
  let V : W.toScheme.Opens := W.ι ⁻¹ᵁ a.opensRange
  have := isNoetherian_of_locallyOfFiniteType (W.toScheme ↘ Spec (CommRingCat.of k₀))
  have : QuasiCompact V.ι := inferInstance
  have := V.isSeparated (k₀ := k₀)
  have := V.locallyOfFiniteType (k₀ := k₀)
  have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over V.ι]
    infer_instance
  have hVfin : ((Set.range V.ι.base)ᶜ).Finite := by
    rw [Scheme.Opens.range_ι]
    refine ((Set.finite_singleton (ProjectiveLine.infinity (Spec (CommRingCat.of k₀))
      (IsLocalRing.closedPoint k₀))).preimage W.ι.isOpenEmbedding.injective.injOn).subset ?_
    intro x hx
    have : W.ι x ∈ ((a.opensRange : Set (ProjectiveLine (Spec (CommRingCat.of k₀))))ᶜ) := hx
    rwa [ProjectiveLine.compl_opensRange_affineChart_eq_singleton] at this
  refine WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_of_upperStar_of_isOpenImmersion
    V.ι hVfin G Nat.one_pos ?_
  -- the open immersion `j : V ⟶ 𝔸¹`
  have hr : Set.range (V.ι ≫ W.ι) ⊆ Set.range a := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  let j : V.toScheme ⟶ affineLine k₀ := IsOpenImmersion.lift a (V.ι ≫ W.ι) hr
  have hj : j ≫ a = V.ι ≫ W.ι := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion j := by
    have : IsOpenImmersion (j ≫ a) := hj ▸ inferInstance
    exact IsOpenImmersion.of_comp j a
  have : j.IsOver (Spec (CommRingCat.of k₀)) := IsOpenImmersion.isOver_lift _ _ hr
  have := isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
  have : QuasiCompact j := inferInstance
  have hjrange : a ⁻¹ᵁ W = j.opensRange := by
    ext x
    change a x ∈ W ↔ x ∈ Set.range j
    constructor
    · intro hx
      obtain ⟨y, hy⟩ : a x ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
      refine ⟨⟨y, ⟨x, hy.symm⟩⟩, a.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hj]
      exact hy
    · rintro ⟨y, rfl⟩
      rw [← Scheme.Hom.comp_apply, hj]
      change W.ι (V.ι y) ∈ (W : Set (ProjectiveLine (Spec (CommRingCat.of k₀))))
      rw [← Scheme.Opens.range_ι W]
      exact Set.mem_range_self (V.ι y)
  have : IsDominant j := by
    have : IrreducibleSpace (affineLine k₀) := inferInstance
    refine ⟨?_⟩
    change Dense (Set.range j)
    rw [← Scheme.Hom.coe_opensRange, ← hjrange]
    refine (a ⁻¹ᵁ W).isOpen.dense ?_
    have hinfty : ProjectiveLine.infinity (Spec (CommRingCat.of k₀)) (IsLocalRing.closedPoint k₀) ∈
        W := by
      have : ProjectiveLine.infinity (Spec (CommRingCat.of k₀)) (IsLocalRing.closedPoint k₀) ∈
          a.opensRange ⊔ W := by rw [hWtop]; trivial
      refine this.resolve_left fun h ↦ ?_
      have h' : ProjectiveLine.infinity (Spec (CommRingCat.of k₀)) (IsLocalRing.closedPoint k₀) ∈
          ((a.opensRange : Set (ProjectiveLine (Spec (CommRingCat.of k₀))))ᶜ) := by
        rw [ProjectiveLine.compl_opensRange_affineChart_eq_singleton]
        rfl
      exact h' h
    have : IrreducibleSpace (ProjectiveLine (Spec (CommRingCat.of k₀))) :=
      GeometricallyIrreducible.irreducibleSpace_of_subsingleton
        (f := ProjectiveLine (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
    obtain ⟨z, ⟨x, rfl⟩, hz⟩ := nonempty_preirreducible_inter a.opensRange.isOpen W.isOpen
      ⟨a (affineLine.origin k₀), ⟨_, rfl⟩⟩ ⟨_, hinfty⟩
    exact ⟨x, hz⟩
  have hinf : ((upperStar V.ι).obj G).IsUnramifiedAtInfinity j :=
    ⟨W, hjrange, hWtop, G, hG, ⟨(upperStarCongr (by
      rw [← cancel_mono W.ι, IsOpenImmersion.lift_fac, hj])).app G⟩⟩
  have hE : ((upperStar V.ι).obj G).IsLisse := hG.upperStar V.ι
  have hEw := hw.upperStar V.ι
  exact hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isUnramifiedAtInfinity ι j
    hE hinf hEw

/-- **Degree one through a quasi-finite map to `ℙ¹`.** Let `U` be a separated `k₀`-scheme of
finite type, `𝓕` a Weil sheaf on `U`, punctually `ι`-pure of weight `w`, `H : U ⟶ ℙ¹` a separated
quasi-finite morphism and `W ⊆ ℙ¹` an open containing `∞`, with finite complement, on which
`H₀!𝓕` is lisse. Then `H_c^1(U, 𝓕)` has weights at most `w + 1`:
`H_c^1(U, 𝓕) = H_c^1(ℙ¹, H₀!𝓕)` is a quotient of `H_c^1(W, (H₀!𝓕)|_W)`, the finite complement of `W`
having no `H_c^1`, and `hasWeightsAtMostOver_compactlySupportedCohomology_one_of_opens_projectiveLine`
applies on `W`. This replaces the constant field extension and the homography of the blueprint
(`lem-a1-unramified-at-infinity`). -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_projectiveLine
    {U : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    (H : U ⟶ ProjectiveLine (Spec (CommRingCat.of k₀))) [H.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated H] [LocallyQuasiFinite H] [LocallyOfFiniteType H] [QuasiCompact H]
    (W : (ProjectiveLine (Spec (CommRingCat.of k₀))).Opens)
    (hWtop : (ProjectiveLine.affineChart (Spec (CommRingCat.of k₀))).opensRange ⊔ W = ⊤)
    (hWfin : ((W : Set (ProjectiveLine (Spec (CommRingCat.of k₀))))ᶜ).Finite) {F : WeilSheaf k₀ l U}
    (hG : ((upperStar W.ι).obj ((higherLowerShriek k₀ l H 0).obj F)).IsLisse)
    {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    (F.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  -- before the local instances below, so that instance arguments agree with those of `hG`
  have hKw : ((higherLowerShriek k₀ l H 0).obj F).IsPunctuallyPureOfWeight ι w :=
    hw.higherLowerShriek_zero_of_quasiFinite (f := H)
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero H F 1
  have := isNoetherian_of_locallyOfFiniteType
    (ProjectiveLine (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀))
  have : QuasiCompact W.ι := inferInstance
  have := W.isSeparated (k₀ := k₀)
  have := W.locallyOfFiniteType (k₀ := k₀)
  have : QuasiCompact (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over W.ι]
    infer_instance
  have hW := hasWeightsAtMostOver_compactlySupportedCohomology_one_of_opens_projectiveLine W
    hWtop hG (hKw.upperStar W.ι)
  have hK := WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_of_upperStar_of_isOpenImmersion
    W.ι (by rwa [Scheme.Opens.range_ι]) _ Nat.one_pos hW
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E hK

/-- **Restricting a quasi-finite direct image to where the map is finite étale.** Let
`H : U ⟶ Y` be a separated quasi-finite morphism of separated `k₀`-schemes of finite type, and
`W ⊆ Y` an open over which `H` is finite étale. If `𝓕` is a lisse Weil sheaf on `U`, then the
restriction `(H₀!𝓕)|_W` is lisse: by base change it is `(H|_W)₀!(𝓕|_{H⁻¹W}) = (H|_W)_*(𝓕|_{H⁻¹W})`,
the direct image of a lisse sheaf along a finite étale morphism.
(blueprint: `lem-a1-reduction-lisse-pure`, lissity) -/
theorem isLisse_upperStar_higherLowerShriek_zero_of_isFinite_of_etale
    {U Y : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (H : U ⟶ Y) [H.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated H] [LocallyQuasiFinite H] [LocallyOfFiniteType H] [QuasiCompact H]
    (W : Y.Opens) [IsFinite (H ∣_ W)] [Etale (H ∣_ W)] {F : WeilSheaf k₀ l U}
    (hF : F.IsLisse) :
    ((upperStar W.ι).obj ((higherLowerShriek k₀ l H 0).obj F)).IsLisse := by
  have : (H ∣_ W).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over W.ι, morphismRestrict_ι_assoc, comp_over H, comp_over (H ⁻¹ᵁ W).ι]⟩
  have := W.isSeparated (k₀ := k₀)
  have := W.locallyOfFiniteType (k₀ := k₀)
  have := (H ⁻¹ᵁ W).isSeparated (k₀ := k₀)
  have := (H ⁻¹ᵁ W).locallyOfFiniteType (k₀ := k₀)
  have := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))
  have := isNoetherian_of_locallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))
  have : QuasiCompact (W.toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over W.ι]
    infer_instance
  have : QuasiCompact ((H ⁻¹ᵁ W).toScheme ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over (H ⁻¹ᵁ W).ι]
    infer_instance
  obtain ⟨e⟩ := nonempty_upperStar_higherLowerShriek_zero_iso
    (isPullback_morphismRestrict H W).flip F
  exact ((hF.upperStar _).lowerStar_of_finite_etale (H ∣_ W)).of_iso
    ((higherLowerShriekZeroObjIsoLowerStar (H ∣_ W) _).symm ≪≫ e.symm)

/-- **Purity of `H_c^2` on an affine curve.** Let `C` be a smooth geometrically connected affine
curve over `k₀` and `𝓕` a lisse Weil sheaf on `C`, punctually `ι`-pure of weight `w`. Then
`H_c^2(C, 𝓕)` is `ι`-pure of weight `w + 2`: it is the degree-two endpoint statement for the
middle extension `(𝟙_C)_* 𝓕 = 𝓕`. (blueprint: `lem-a1-affine-hc2-pure`) -/
theorem IsPunctuallyPureOfWeight.isPureOfWeightOver_compactlySupportedCohomology_two
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l C}
    (hF : F.IsLisse) {w : ℝ} (hw : F.IsPunctuallyPureOfWeight ι w) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    (F.compactlySupportedCohomology 2).IsPureOfWeightOver k₀ ι (w + 2) := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have h := isPureOfWeightOver_compactlySupportedCohomology_directImage_two (𝟙 C) F ι hF hw
  obtain ⟨e⟩ := nonempty_equiv_compactlySupportedCohomology_of_iso
    ((lowerStarIdIso k₀ l C).app F) 2
  exact FrobeniusModule.IsPureOfWeight.of_equiv e.symm h

/-- **Vanishing outside degrees one and two on an affine curve.** Let `C` be a smooth
geometrically connected affine curve over `k₀` and `𝓕` a lisse Weil sheaf on `C`. Then
`H_c^r(C, 𝓕) = 0` for `r ∉ {1, 2}`. (blueprint: `lem-a1-affine-hc0`, `lem-zl-affine-curve-range`) -/
theorem subsingleton_compactlySupportedCohomology_of_isLisse_of_isAffine
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (C ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l C}
    (hF : F.IsLisse) {r : ℤ} (hr : r ≤ 0 ∨ 2 < r) :
    haveI := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
    Subsingleton (F.compactlySupportedCohomology r).carrier := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  rcases hr with hr | hr
  · rcases hr.lt_or_eq with hr | rfl
    · exact subsingleton_compactlySupportedCohomology_of_isAffine F (Or.inl hr)
    · exact subsingleton_compactlySupportedCohomology_zero F hF
  · exact subsingleton_compactlySupportedCohomology_of_isAffine F (Or.inr hr)

namespace LisseOnDenseOpen

/-- **Degree one on a dense open of the line.** Let `𝓕` be lisse on the dense open `U₀ ⊆ 𝔸¹`,
punctually `ι`-pure of weight `w`. Then `H_c^1(U, 𝓕)` has weights at most `w + 1`, with no
condition at infinity: a separated quasi-finite map `H : U₀ ⟶ ℙ¹` sends a closed point of `U₀` to
`∞` and is finite étale over an open `W ∋ ∞`, so that `(H₀!𝓕)|_W` is lisse, and
`hasWeightsAtMostOver_compactlySupportedCohomology_one_of_projectiveLine` applies. This replaces
the constant field extension and the homography of the blueprint.
(blueprint: `lem-a1-unramified-at-infinity`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isPunctuallyPureOfWeight
    (D : LisseOnDenseOpen k₀ l) {w : ℝ} (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) :
    (D.sheaf.compactlySupportedCohomology 1).HasWeightsAtMostOver k₀ ι (w + 1) := by
  sorry

/-- **The compact-support upper bound on a dense open of the line.** Let `𝓕` be lisse on the
dense open `U₀ ⊆ 𝔸¹`, punctually `ι`-pure of weight `w`. Then `H_c^r(U, 𝓕)` has weights at most
`w + r` for every `r`; it vanishes for `r ∉ {1, 2}` and is pure of weight `w + 2` for `r = 2`.
This is the case of the line of `thm-a1-affine-curve-upper`. -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology (D : LisseOnDenseOpen k₀ l) {w : ℝ}
    (hw : D.sheaf.IsPunctuallyPureOfWeight ι w) (r : ℤ) :
    (D.sheaf.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι (w + r) := by
  rcases lt_trichotomy r 1 with hr | rfl | hr
  · have := subsingleton_compactlySupportedCohomology_of_isLisse_of_isAffine D.lisse
      (Or.inl (by omega : r ≤ 0))
    exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
  · exact_mod_cast D.hasWeightsAtMostOver_compactlySupportedCohomology_one_of_isPunctuallyPureOfWeight
      hw
  · rcases (by omega : 2 < r ∨ r = 2) with hr | rfl
    · have := subsingleton_compactlySupportedCohomology_of_isLisse_of_isAffine D.lisse (Or.inr hr)
      exact FrobeniusModule.hasWeightsAtMost_of_subsingleton _ _ _
    · exact_mod_cast (hw.isPureOfWeightOver_compactlySupportedCohomology_two D.lisse).hasWeightsAtMostOver

end LisseOnDenseOpen

/-- **Exceptional rank-one constituents.** Let `j : U₀ ⟶ 𝔸¹` be a dense open immersion and `𝓔` a
Weil sheaf on `U₀` which is either a constant twist `ℚ̄_ℓ(b)` of the constant sheaf or the
restriction of a twisted Artin–Schreier sheaf `ℒ_{ψ(a x)}(b)` with `a ≠ 0`. If `𝓔` is punctually
`ι`-pure of weight `w`, then `H_c^i(U, 𝓔)` has weights at most `w + i` for every `i`: `𝓔` is
lisse, and the estimate on dense opens of the line applies. The blueprint computes the
cohomology of the line instead; the general estimate makes this unnecessary.
(blueprint: `lem-a1-exceptional-constituents`) -/
theorem hasWeightsAtMostOver_compactlySupportedCohomology_of_exceptional {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))] [IsDominant j]
    (ψ : AddChar k₀ (PadicAlgCl l)) (b : (PadicAlgCl l)ˣ) {E : WeilSheaf k₀ l U}
    (hE : Nonempty (E ≅ (adicConstant k₀ l U).constantTwist b) ∨
      ∃ a : k₀, a ≠ 0 ∧ Nonempty (E ≅ (upperStar j).obj ((artinSchreier ψ a).constantTwist b)))
    {w : ℝ} (hw : E.IsPunctuallyPureOfWeight ι w) (i : ℤ) :
    haveI : LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over j]; infer_instance
    haveI : IsSeparated (U ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over j]; infer_instance
    haveI : QuasiCompact (U ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over j]; infer_instance
    (E.compactlySupportedCohomology i).HasWeightsAtMostOver k₀ ι (w + i) := by
  have hE' : E.IsLisse := by
    rcases hE with ⟨⟨e⟩⟩ | ⟨a, -, ⟨e⟩⟩
    · exact (IsLisse.constantTwist (isLisse_adicConstant k₀ l U)).of_iso e.symm
    · exact (((isLisse_artinSchreier ψ a).constantTwist).upperStar j).of_iso e.symm
  exact LisseOnDenseOpen.hasWeightsAtMostOver_compactlySupportedCohomology ⟨U, j, E, hE'⟩ hw i

/-- **Subquotients of pure sheaves are pure.** If `𝓖` is punctually `ι`-pure of weight `w` and
`𝓢` is a subquotient of `𝓖`, a quotient `A ↠ 𝓢` of a subobject `A ↪ 𝓖`, then `𝓢` is punctually
`ι`-pure of weight `w`: its stalks are Frobenius-stable subquotients of those of `𝓖`.
(blueprint: `lem-a1-subquotient-pure`) -/
theorem IsPunctuallyPureOfWeight.of_subquotient {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    {G A S : WeilSheaf k₀ l X} (i : A ⟶ G) [Mono i] (p : A ⟶ S) [Epi p] {w : ℝ}
    (h : G.IsPunctuallyPureOfWeight ι w) : S.IsPunctuallyPureOfWeight ι w :=
  (h.of_mono i).of_epi p

end WeilSheaf

end AlgebraicGeometry
