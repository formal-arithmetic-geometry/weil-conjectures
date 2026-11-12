/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.GaloisFieldCover
public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.WeilSheaf.UpperStarSurjective

/-!
# Descending mixedness along finite constant extensions and open–closed decompositions

Two ways of recovering mixedness of a constructible Weil sheaf `G` on `X₀` from mixedness of
its pullbacks, used to splice together the filtrations with pure quotients in the proof that
real sheaves are mixed (blueprint section `sec-Mixedness-of-real-sheaves`):

- along a finite constant extension `g : X₀ ⊗_{k₀} k_m ⟶ X₀`: the unit `G ⟶ g_* g^* G` is a
  monomorphism, `g` being surjective and finite étale, and `g_* g^* G` is mixed since `g` is
  finite;
- along an open immersion `j : U₀ ⟶ X₀` and its closed complement `i : Z₀ ⟶ X₀`: this is the
  open–closed exact sequence `0 ⟶ j_! j^* G ⟶ G ⟶ i_* i^* G ⟶ 0`
  (`AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed`).

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsMixed.of_upperStar_of_isPullback`: blueprint
  `lemma-mixedness-descends-constant-extension`.
- `AlgebraicGeometry.WeilSheaf.IsMixed.of_openClosed`: blueprint `lemma-mixedness-open-closed`.

## Implementation notes

The scheme `X₀ ⊗_{k₀} k_m` is regarded as a `k₀`-scheme through `g`, and `g^* G` is the pullback
of Weil sheaves relative to `k₀`; a Weil sheaf on a `k_m`-scheme relative to `k₀` is the same as
one relative to `k_m` (`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctor`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ} {X X' : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]

/-- The direct image `g₀*` along a finite morphism `g` of `k₀`-schemes carries Weil sheaves mixed
of weights at most `w` to Weil sheaves mixed of weights at most `w`: `g₀* G` is the cohomology
sheaf `𝓗⁰(Rg₀* G)` of the finite pushforward of `G` placed in degree zero
(`AlgebraicGeometry.WeilComplex.IsMixedOfWeightsAtMost.derivedLowerStar_of_isFinite`). -/
theorem IsMixedOfWeightsAtMost.lowerStar_of_isFinite (g : X' ⟶ X) [IsFinite g]
    [g.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {w : ℝ} {G : WeilSheaf k₀ l X'} (hG : G.IsMixedOfWeightsAtMost ι w) :
    ((WeilSheaf.lowerStar g).obj G).IsMixedOfWeightsAtMost ι w := by
  rw [← WeilComplex.isMixedOfWeightsAtMost_toComplex_iff] at hG
  simpa using (hG.derivedLowerStar_of_isFinite g 0).of_iso
    (homologySheafZeroDerivedLowerStarIso g G)

/-- Let `g : X' ⟶ X` be a surjective finite étale morphism of `k₀`-schemes and `G` a Weil sheaf
on `X`. If `g^* G` is mixed of weights at most `w`, then so is `G`: it is a subobject of
`g_* g^* G` through the unit of `g^* ⊣ g_*`
(`AlgebraicGeometry.WeilSheaf.mono_upperStarLowerStarAdjunction_unit_app_of_surjective`), and
`g_* g^* G` is mixed of weights at most `w` since `g` is finite. -/
theorem IsMixedOfWeightsAtMost.of_upperStar_of_surjective (g : X' ⟶ X) [IsFinite g] [Etale g]
    [Surjective g] [g.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {w : ℝ} {G : WeilSheaf k₀ l X}
    (hG : ((WeilSheaf.upperStar g).obj G).IsMixedOfWeightsAtMost ι w) :
    G.IsMixedOfWeightsAtMost ι w := by
  have := mono_upperStarLowerStarAdjunction_unit_app_of_surjective (l := l) g G
  exact (hG.lowerStar_of_isFinite g).of_mono
    ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).unit.app G)

/-- Let `g : X' ⟶ X` be a surjective finite étale morphism of `k₀`-schemes and `G` a Weil sheaf
on `X`. If `g^* G` is mixed, then so is `G`. -/
theorem IsMixed.of_upperStar_of_surjective (g : X' ⟶ X) [IsFinite g] [Etale g] [Surjective g]
    [g.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {G : WeilSheaf k₀ l X} (hG : ((WeilSheaf.upperStar g).obj G).IsMixed ι) : G.IsMixed ι :=
  let ⟨w, hw⟩ := hG
  ⟨w, hw.of_upperStar_of_surjective g⟩

/-- **Mixedness descends along finite constant extensions** (blueprint:
`lemma-mixedness-descends-constant-extension`). Let `k'` be a finite extension of the finite
field `k₀`, let `g : X' ⟶ X` be the finite constant extension `X' = X ⊗_{k₀} k' ⟶ X` of a
`k₀`-scheme `X` of finite type, exhibited by the pullback square `hg`, and let `G` be a Weil sheaf
on `X`. If `g^* G` is `ι`-mixed, then so is `G`.

The unit `G ⟶ g_* g^* G` is a monomorphism and `g_* g^* G` is mixed since `g` is finite
(`AlgebraicGeometry.WeilSheaf.IsMixed.of_upperStar_of_surjective`).

The instance arguments `[X'.Over k₀]` and `[LocallyOfFiniteType (X' ↘ _)]` carry no extra
assumption: given `[g.IsOver k₀]`, the structure morphism of `X'` is `g` followed by that of `X`,
and it is locally of finite type since `g` is the base change of the finite morphism
`Spec k' ⟶ Spec k₀` along `hg`. -/
theorem IsMixed.of_upperStar_of_isPullback (k' : Type u) [Field k'] [Finite k'] [Algebra k₀ k']
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (g : X' ⟶ X)
    [g.IsOver (Spec (CommRingCat.of k₀))] (p : X' ⟶ Spec (CommRingCat.of k'))
    (hg : IsPullback g p (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k'))))
    {G : WeilSheaf k₀ l X} (hG : ((WeilSheaf.upperStar g).obj G).IsMixed ι) : G.IsMixed ι := by
  have : FiniteDimensional k₀ k' := .of_finite
  have : IsFinite g := MorphismProperty.of_isPullback hg.flip inferInstance
  have : Etale g := MorphismProperty.of_isPullback hg.flip inferInstance
  have : Surjective g := MorphismProperty.of_isPullback hg.flip inferInstance
  exact hG.of_upperStar_of_surjective g

/-- **Mixedness on an open and its complement** (blueprint: `lemma-mixedness-open-closed`). Let
`j : U ⟶ X` be a quasi-compact open immersion of `k₀`-schemes whose closed complement is
`i : Z ⟶ X`, and let `G` be a Weil sheaf on `X`. If `j^* G` and `i^* G` are `ι`-mixed, then so
is `G`: both are mixed of weights at most the larger of their two bounds, and the form with a
common weight bound, `AlgebraicGeometry.WeilSheaf.IsMixedOfWeightsAtMost.of_openClosed`
(blueprint: `lemma-mixedness-open-closed--1`), applies. -/
theorem IsMixed.of_openClosed {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    {j : U ⟶ X} [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {i : Z ⟶ X} [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) {G : WeilSheaf k₀ l X}
    (hU : ((WeilSheaf.upperStar j).obj G).IsMixed ι)
    (hZ : ((WeilSheaf.upperStar i).obj G).IsMixed ι) : G.IsMixed ι :=
  let ⟨w₁, h₁⟩ := hU
  let ⟨w₂, h₂⟩ := hZ
  ⟨max w₁ w₂, IsMixedOfWeightsAtMost.of_openClosed hij (h₁.mono_weight (le_max_left _ _))
    (h₂.mono_weight (le_max_right _ _))⟩

end AlgebraicGeometry.WeilSheaf
