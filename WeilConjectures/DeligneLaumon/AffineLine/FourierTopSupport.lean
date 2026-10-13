/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters
public import WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.StalkExtensionByZero
public import WeilConjectures.WeilSheaf.SupportSubobject

/-!
# The top cohomology sheaf of the Fourier transform has finite support

Let `K` be a Weil complex on the affine line concentrated in degrees `≤ m`. Then `FT_ψ(K)` is
concentrated in degrees `≤ m + 1`, and its top cohomology sheaf `H = 𝓗^{m+1} FT_ψ(K)` has finite
support (`AlgebraicGeometry.support_homologySheaf_fourierTransform_finite`, the key step 1(a) of
blueprint `thm-a1-fourier-t-exact`).

The blueprint computes the stalk of `H` at a geometric point `ξ` as
`H²_c(U, F ⊗ ℒ_{ψ(ξ x)})`, the coinvariants of `F ⊗ ℒ_{ψ(ξ x)}`, and counts the linear
characters which are quotients of `F`. We argue by Fourier inversion instead, which avoids the
stalks at points which are not `k₀`-rational:

- for a closed point `x` in the support of `H`, the closed complement `i : Z₀ ↪ 𝔸¹` of
  `V₀ = 𝔸¹ ∖ {x}` gives a nonzero morphism `H ⟶ i_* i^* H`, from the open–closed triangle and
  the vanishing of the stalk of `j_! j^* H` at `x`;
- the composite `FT_ψ(K) ⟶ H[-m-1] ⟶ (i_* i^* H)[-m-1]` is nonzero; applying `FT_{ψ⁻¹}` and
  Fourier inversion, it becomes a nonzero morphism `N ⟶ B` from `N = 𝓗^m(K(-1))` to the lisse
  sheaf `B[1] = FT_{ψ⁻¹}(i_* i^* H)`, which is geometrically a sum of linear characters
  `ℒ_{ψ(a x)}` with `-a` the coordinate of a geometric point over `x`
  (`AlgebraicGeometry.WeilSheaf.exists_iso_carrier_lowerStar_tensorObj_fourierKernel_inv`);
- on the geometric fibre `Ū` of a dense open on which `N` is lisse, `N` therefore has a nonzero
  morphism to some `ℒ_{ψ(a x)}|_Ū` with `a` over `x`. These characters are irreducible and
  pairwise distinct (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isEmpty_iso_linearCharacter`),
  so there are at most `rank N|_U` of them
  (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.le_finrank_of_ne_zero`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable (k₀) in
/-- `a ∈ k̄` is minus the coordinate of a geometric point of the affine line over the closed
point `x`. -/
def affineLine.IsNegCoordOver (a : AlgebraicClosure k₀) (x : (affineLine k₀).finitePoints) :
    Prop :=
  ∃ t : Spec (.of (AlgebraicClosure k₀)) ⟶ affineLine k₀,
    t ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = (Scheme.specAlgebraicClosure k₀).hom ∧
      t.base (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 ∧
        a = -affineLine.coordOfPoint t

omit [Finite k₀] in
/-- A geometric point of the affine line over `k̄` is determined by its coordinate, so an element
of `k̄` lies over at most one closed point. -/
theorem affineLine.IsNegCoordOver.eq {a : AlgebraicClosure k₀}
    {x y : (affineLine k₀).finitePoints} (hx : affineLine.IsNegCoordOver k₀ a x)
    (hy : affineLine.IsNegCoordOver k₀ a y) : x = y := by
  obtain ⟨t, ht, hxt, rfl⟩ := hx
  obtain ⟨t', ht', hyt, ha⟩ := hy
  have hc : affineLine.coordOfPoint t = affineLine.coordOfPoint t' := neg_injective ha
  have : t = t' := by
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · exact ht.trans ht'.symm
    · exact (Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).commRingCatIsoToRingEquiv.injective hc
  subst this
  exact Subtype.ext (hxt.symm.trans hyt)

namespace WeilComplex

/-- **The restriction to a closed point in the support is nonzero.** Let `j : V₀ ↪ 𝔸¹` be an open
immersion missing a closed point `x` in the support of a Weil sheaf `G`, and let
`j_!j^*G ⟶ G ⟶ C ⟶` be a distinguished triangle (for instance the open–closed triangle). Then
`G ⟶ C` is nonzero: otherwise `G` would be a direct summand of `j_!j^*G`, whose stalk at `x`
vanishes. -/
theorem mor₂_ne_zero_of_mem_support {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
    (j : V ⟶ affineLine k₀) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l (affineLine k₀))
    (x : (affineLine k₀).finitePoints) (hxG : x ∈ G.support) (hxj : x.1 ∉ Set.range j.base)
    {C : WeilComplex k₀ l (affineLine k₀)}
    (α : (derivedLowerShriek k₀ l j).obj ((upperStar j).obj (WeilSheaf.toComplex.obj G)) ⟶
      (derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G))
    (β : (derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G) ⟶ C)
    (γ : C ⟶ ((derivedLowerShriek k₀ l j).obj
      ((upperStar j).obj (WeilSheaf.toComplex.obj G)))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk α β γ ∈ distTriang _) : β ≠ 0 := by
  intro hβ
  obtain ⟨r, hr⟩ := Triangle.coyoneda_exact₂ _ hT (𝟙 _) (by simp [hβ])
  obtain ⟨eId⟩ := nonempty_derivedLowerShriekIdIso (k₀ := k₀) (l := l) (affineLine k₀)
  obtain ⟨eZ⟩ := nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion (l := l) j
    ((WeilSheaf.upperStar j).obj G)
  let H0 := homologySheaf (k₀ := k₀) (l := l) (X := affineLine k₀) 0
  let e₁ : H0.obj ((derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G)) ≅ G :=
    H0.mapIso (eId.app _) ≪≫ WeilSheaf.toComplexCompHomologySheafIso.app G
  let e₂ : H0.obj ((derivedLowerShriek k₀ l j).obj ((upperStar j).obj
      (WeilSheaf.toComplex.obj G))) ≅ (WeilSheaf.extensionByZero j).obj
        ((WeilSheaf.upperStar j).obj G) :=
    H0.mapIso ((derivedLowerShriek k₀ l j).mapIso
      ((WeilSheaf.toComplexCompUpperStarIso j).app G) ≪≫ eZ) ≪≫
      WeilSheaf.toComplexCompHomologySheafIso.app _
  let s : G ⟶ (WeilSheaf.extensionByZero j).obj ((WeilSheaf.upperStar j).obj G) :=
    e₁.inv ≫ H0.map r ≫ e₂.hom
  have hs : s ≫ (e₂.inv ≫ H0.map α ≫ e₁.hom) = 𝟙 _ := by
    simp only [s, Category.assoc, Iso.hom_inv_id_assoc]
    have hr' : r ≫ α = 𝟙 ((derivedLowerShriek k₀ l (𝟙 _)).obj (WeilSheaf.toComplex.obj G)) :=
      hr.symm
    rw [← H0.map_comp_assoc, hr', H0.map_id, Category.id_comp, Iso.inv_hom_id]
  have : Mono s := mono_of_mono_fac hs
  have hx := WeilSheaf.support_subset_of_mono s hxG
  exact (not_subsingleton_iff_nontrivial.2 hx)
    (WeilSheaf.subsingleton_stalk_extensionByZero j _ x hxj)

end WeilComplex

end AlgebraicGeometry
