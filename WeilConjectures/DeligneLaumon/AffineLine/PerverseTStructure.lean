/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Perverse
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# The perverse t-structure on the affine line and the abelian category of perverse Weil sheaves

On a smooth curve `C₀` over `k₀`, the curve perverse classes of
`WeilConjectures.DeligneLaumon.AffineLine.Perverse`,

* `ᵖD^{≤n}`: `𝓗ᵃK = 0` for `a > n` and `𝓗ⁿK` has finite support,
* `ᵖD^{≥n}`: `𝓗ᵃK = 0` for `a < n - 1` and `𝓗ⁿ⁻¹K` has no nonzero subsheaf of finite support,

form a t-structure on the triangulated category of Weil complexes as soon as every Weil sheaf
`F` has a largest punctual subsheaf, that is, a quotient `F ↠ Q` with punctual kernel and
without nonzero punctual subsheaf (`AlgebraicGeometry.WeilComplex.exists_distTriang_curvePerverse`).
Following the blueprint, the truncation triangle of a Weil complex `A` is obtained from the
ordinary truncation `τ^{≤0}A ⟶ A ⟶ τ^{≥1}A ⟶` by splitting off the punctual part of `𝓗⁰A`
with the octahedral axiom. On the affine line the largest punctual subsheaf of `F` is the kernel
of the unit `F ⟶ j_*j^*F` of a dense open `j` on which `F` is lisse
(`AlgebraicGeometry.WeilSheaf.exists_epi_support_finite_kernel`).

The heart of this t-structure is the category of curve perverse Weil complexes, that is, of
perverse Weil sheaves; it is therefore abelian (blueprint `lemma-perverse-weil-sheaves`, part 1).

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsCurvePerverseGE`: the shifted lower classes `ᵖD^{≥n}`.
- `AlgebraicGeometry.WeilComplex.curvePerverseTStructure`: the perverse t-structure on Weil
  complexes on the affine line.
- `AlgebraicGeometry.WeilComplex.curvePerverseTStructure_heart`: its heart is the class of curve
  perverse Weil complexes.
- `AlgebraicGeometry.WeilComplex.abelianCurvePerverse`: perverse Weil sheaves on the affine line
  form an abelian category.

## Implementation notes

The blueprint states the lemma for a smooth curve `C₀`. Here the Weil sheaf input, the largest
punctual subsheaf (blueprint `lemma-largest-punctual-subsheaf`), is available on the affine line,
the curve of the Fourier transform; the construction of the truncation triangles is stated for an
arbitrary smooth curve under that input.

In this formalisation a Weil complex carries its Weil structure (`AlgebraicGeometry.WeilComplex`
is the derived category of Weil sheaves), so the perverse Weil sheaves are the heart of the
t-structure on Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Triangulated

namespace AlgebraicGeometry

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The largest punctual subsheaf** on the affine line: every Weil sheaf `F` has a quotient
`p : F ↠ Q` with punctual kernel and without nonzero punctual subsheaf. On a dense open
`j : U₀ ↪ 𝔸¹` where `F` is lisse, `Q` is the image of the unit `F ⟶ j_*j^*F`: the kernel of the
unit vanishes on `U₀`, and a punctual subsheaf of `j_*j^*F` vanishes.
(blueprint: `lemma-largest-punctual-subsheaf`) -/
theorem exists_epi_support_finite_kernel (F : WeilSheaf k₀ l (affineLine k₀)) :
    ∃ (Q : WeilSheaf k₀ l (affineLine k₀)) (p : F ⟶ Q), Epi p ∧ (kernel p).support.Finite ∧
      ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ Q), Mono i → G.support.Finite →
        IsZero G := by
  have : IsNoetherian (affineLine k₀) :=
    isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (.of k₀))
  obtain ⟨U, hU, hUl⟩ := exists_dense_isLisse_upperStar F
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  set η := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) U.ι).unit.app F
  refine ⟨Limits.image η, factorThruImage η, inferInstance, ?_, fun G i _ hG ↦ ?_⟩
  · rw [← support_congr (kernelIsoOfEq (Limits.image.fac η).symm ≪≫
      kernelCompMono (factorThruImage η) (Limits.image.ι η))]
    exact support_finite_kernel_unit_app U.ι F
  · exact IsZero.of_mono_eq_zero (i ≫ Limits.image.ι η)
      (eq_zero_of_support_finite_lowerStar U.ι hUl hG _)

end WeilSheaf

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The shifted lower class `ᵖD^{≥n} = ᵖD^{≥0}[-n]` of the perverse t-structure on a smooth
curve: `𝓗ᵃK = 0` for `a < n - 1`, and `𝓗ⁿ⁻¹K` has no nonzero subsheaf of finite support.
(blueprint: `definition-perverse-sheaves-curve`) -/
def IsCurvePerverseGE (n : ℤ) (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < n - 1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (n - 1)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

theorem isCurvePerverseLower_iff_isCurvePerverseGE_zero (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseLower ↔ K.IsCurvePerverseGE 0 :=
  Iff.rfl

theorem IsCurvePerverseGE.of_iso {n : ℤ} {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (hK : K.IsCurvePerverseGE n) : L.IsCurvePerverseGE n :=
  ⟨fun a ha ↦ (hK.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
    fun G i _ hG ↦ hK.2 G (i ≫ ((homologySheaf (n - 1)).mapIso e).inv) inferInstance hG⟩

/-- The shifted classes `ᵖD^{≥n}` are compatible with the shift: `K[m] ∈ ᵖD^{≥n'}` for
`K ∈ ᵖD^{≥n}` and `m + n' = n`. -/
theorem IsCurvePerverseGE.shift {n : ℤ} {K : WeilComplex k₀ l X} (hK : K.IsCurvePerverseGE n)
    (m n' : ℤ) (h : m + n' = n) : (K⟦m⟧).IsCurvePerverseGE n' :=
  ⟨fun a ha ↦ (hK.1 (m + a) (by lia)).of_iso (homologySheafShiftIso K m a (m + a) rfl),
    fun G i _ hG ↦ hK.2 G (i ≫ (homologySheafShiftIso K m (n' - 1) (n - 1) (by lia)).hom)
      inferInstance hG⟩

section Curve

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Orthogonality** of the perverse classes on a smooth curve: there is no nonzero morphism
from `ᵖD^{≤0}` to `ᵖD^{≥1}`. (blueprint: `lemma-perverse-sheaves-curve`) -/
theorem eq_zero_of_isCurvePerverseLE_of_isCurvePerverseGE {M K : WeilComplex k₀ l X}
    (hM : M.IsCurvePerverseLE 0) (hK : K.IsCurvePerverseGE 1) (f : M ⟶ K) : f = 0 := by
  apply (shiftFunctor (WeilComplex k₀ l X) (1 : ℤ)).map_injective
  rw [Functor.map_zero]
  exact (isCurvePerverseLower_iff_forall_hom_eq_zero _).1 (hK.shift 1 0 (by lia)) _
    (hM.shift 1 (-1) (by lia)) _

/-- **The perverse truncation triangle** on a scheme on which every Weil sheaf has a largest
punctual subsheaf: every Weil complex `A` sits in a distinguished triangle
`A' ⟶ A ⟶ A'' ⟶ A'[1]` with `A' ∈ ᵖD^{≤0}` and `A'' ∈ ᵖD^{≥1}`. With `K' = τ^{≤0}A` and
`F = 𝓗⁰A ↠ Q` the quotient by the largest punctual subsheaf, `A'` is the fibre of
`K' ⟶ Q[0]`, and the octahedral axiom exhibits `A''` as an extension of `τ^{≥1}A` by `Q[0]`.
(blueprint: `lemma-perverse-sheaves-curve`) -/
theorem exists_distTriang_curvePerverse
    (hX : ∀ F : WeilSheaf k₀ l X, ∃ (Q : WeilSheaf k₀ l X) (p : F ⟶ Q), Epi p ∧
      (kernel p).support.Finite ∧
      ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ Q), Mono i → G.support.Finite → IsZero G)
    (A : WeilComplex k₀ l X) :
    ∃ (A' A'' : WeilComplex k₀ l X) (_ : A'.IsCurvePerverseLE 0) (_ : A''.IsCurvePerverseGE 1)
      (f : A' ⟶ A) (g : A ⟶ A'') (h : A'' ⟶ A'⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _ := by
  -- the ordinary truncation triangle `K' ⟶ A ⟶ Z ⟶ K'[1]`
  obtain ⟨K', Z, a, b, c, hT₂, hK', hZ, -, -⟩ := exists_distTriang_truncLT A 1
  have hK'0 (n : ℤ) (hn : 0 < n) : IsZero ((homologySheaf n).obj K') :=
    (isZero_homologySheaf_obj_iff n K').2
      ((_root_.DerivedCategory.isLE_iff _ (1 - 1)).1 hK' n (by lia))
  have hZ0 (n : ℤ) (hn : n < 1) : IsZero ((homologySheaf n).obj Z) :=
    (isZero_homologySheaf_obj_iff n Z).2 ((_root_.DerivedCategory.isGE_iff _ 1).1 hZ n hn)
  -- the quotient `𝓗⁰K' ↠ Q` by the largest punctual subsheaf, and `q : K' ⟶ Q[0]`
  obtain ⟨Q, p, _, hkp, hQ⟩ := hX ((homologySheaf 0).obj K')
  let eQ := WeilSheaf.toComplexCompHomologySheafIso.app Q
  have hQn (n : ℤ) (hn : n ≠ 0) :
      IsZero ((homologySheaf n).obj (WeilSheaf.toComplex.obj Q)) :=
    isZero_homologySheaf_singleComplex hn Q
  obtain ⟨q, hq⟩ := (homologySheaf_map_bijective 0 (K := K')
    (L := WeilSheaf.toComplex.obj Q) hK'0 (fun n hn ↦ hQn n hn.ne)).2 (p ≫ eQ.inv)
  simp only at hq
  -- the triangle `A' ⟶ K' ⟶ Q[0] ⟶ A'[1]`
  obtain ⟨A', u, w, hT₁⟩ := distinguished_cocone_triangle₁ q
  obtain ⟨A'', g, h, hT₃⟩ := distinguished_cocone_triangle (u ≫ a)
  have oct := someOctahedron rfl hT₁ hT₂ hT₃
  set T₁ := Triangle.mk u q w
  set T₄ := Triangle.mk oct.m₁ oct.m₃ (c ≫ q⟦(1 : ℤ)⟧')
  have hT₄ : T₄ ∈ distTriang _ := oct.mem
  refine ⟨A', A'', ⟨fun n hn ↦ ?_, ?_⟩, ⟨fun n hn ↦ ?_, fun G i _ hG ↦ ?_⟩, u ≫ a, g, h, hT₃⟩
  · -- `𝓗ⁿA' = 0` for `n > 0`: it is the image of `𝓗ⁿ⁻¹(Q[0]) ⟶ 𝓗ⁿA'`, which vanishes
    obtain rfl | hn' := eq_or_lt_of_le (show 1 ≤ n by lia)
    · have := (homologySheaf_exact₁ T₁ 0 1 hT₁ rfl).epi_f ((hK'0 1 one_pos).eq_of_tgt _ _)
      refine IsZero.of_epi_eq_zero (homologySheafδ T₁ 0 1 rfl) ?_
      have : Epi ((homologySheaf 0).map T₁.mor₂) := by
        change Epi ((homologySheaf 0).map q)
        rw [hq]
        infer_instance
      rw [← cancel_epi ((homologySheaf 0).map T₁.mor₂), comp_zero]
      exact homologySheaf_map_mor₂_comp_δ T₁ 0 1 hT₁ rfl
    · have := (homologySheaf_exact₁ T₁ (n - 1) n hT₁ (by lia)).epi_f
        ((hK'0 n hn).eq_of_tgt _ _)
      exact IsZero.of_epi_eq_zero (homologySheafδ T₁ (n - 1) n (sub_add_cancel n 1))
        ((hQn (n - 1) (by lia)).eq_of_src _ _)
  · -- `𝓗⁰A'` embeds into the punctual kernel of `𝓗⁰K' ⟶ Q`
    have : Mono ((homologySheaf 0).map u) :=
      (homologySheaf_exact₁ T₁ (-1) 0 hT₁ (by norm_num)).mono_g
        ((hQn (-1) (by norm_num)).eq_of_src _ _)
    have h0 : u ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT₁
    have hw : (homologySheaf 0).map u ≫ (p ≫ eQ.inv) = 0 := by
      rw [← hq, ← Functor.map_comp, h0, Functor.map_zero]
    have : Mono (kernel.lift _ _ hw) := mono_of_mono_fac (kernel.lift_ι _ _ hw)
    refine Set.Finite.subset ?_ (WeilSheaf.support_subset_of_mono (kernel.lift _ _ hw))
    rw [WeilSheaf.support_congr (kernelCompMono p eQ.inv)]
    exact hkp
  · -- `𝓗ⁿA'' = 0` for `n < 0`, as it is an extension of `𝓗ⁿZ` by `𝓗ⁿ(Q[0])`
    exact (homologySheaf_exact₂ T₄ n hT₄).isZero_X₂ ((hQn n (by lia)).eq_of_src _ _)
      ((hZ0 n (by lia)).eq_of_tgt _ _)
  · -- `𝓗⁰A'' ≅ Q` has no nonzero punctual subsheaf
    have : Mono ((homologySheaf 0).map oct.m₁) :=
      (homologySheaf_exact₁ T₄ (-1) 0 hT₄ (by norm_num)).mono_g
      ((hZ0 (-1) (by norm_num)).eq_of_src _ _)
    have : Epi ((homologySheaf 0).map oct.m₁) :=
      (homologySheaf_exact₂ T₄ 0 hT₄).epi_f ((hZ0 0 (by norm_num)).eq_of_tgt _ _)
    have : IsIso ((homologySheaf 0).map oct.m₁) := isIso_of_mono_of_epi _
    exact hQ G (i ≫ inv ((homologySheaf 0).map oct.m₁) ≫ eQ.hom) inferInstance hG

end Curve

section AffineLine

/-- **The perverse t-structure on the affine line**: the classes `ᵖD^{≤n}` and `ᵖD^{≥n}` form a
t-structure on the triangulated category of Weil complexes on `𝔸¹_{k₀}`. Orthogonality is
`AlgebraicGeometry.WeilComplex.eq_zero_of_isCurvePerverseLE_of_isCurvePerverseGE`, and the
truncation triangles are `AlgebraicGeometry.WeilComplex.exists_distTriang_curvePerverse`.
(blueprint: `lemma-perverse-sheaves-curve`) -/
noncomputable def curvePerverseTStructure : TStructure (WeilComplex k₀ l (affineLine k₀)) where
  le n K := K.IsCurvePerverseLE n
  ge n K := K.IsCurvePerverseGE n
  le_isClosedUnderIsomorphisms _ := ⟨fun e h ↦ IsCurvePerverseLE.of_iso e h⟩
  ge_isClosedUnderIsomorphisms _ := ⟨fun e h ↦ IsCurvePerverseGE.of_iso e h⟩
  le_shift _ a n' h _ hK := IsCurvePerverseLE.shift hK a n' h
  ge_shift _ a n' h _ hK := IsCurvePerverseGE.shift hK a n' h
  zero' _ _ f hK hL :=
    have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
      simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
    eq_zero_of_isCurvePerverseLE_of_isCurvePerverseGE hK hL f
  le_zero_le K hK := ⟨fun a ha ↦ hK.1 a (by lia), by
    rw [WeilSheaf.support_eq_empty_of_isZero (hK.1 1 one_pos)]
    exact Set.finite_empty⟩
  ge_one_le K hK := ⟨fun a ha ↦ hK.1 a (by lia),
    fun _ i _ _ ↦ IsZero.of_mono i (hK.1 (0 - 1) (by norm_num))⟩
  exists_triangle_zero_one A :=
    exists_distTriang_curvePerverse WeilSheaf.exists_epi_support_finite_kernel A

/-- The heart of the perverse t-structure on the affine line is the class of curve perverse Weil
complexes, the perverse Weil sheaves. (blueprint: `definition-perverse-sheaves-curve`) -/
theorem curvePerverseTStructure_heart :
    (curvePerverseTStructure (k₀ := k₀) (l := l)).heart = curvePerverse :=
  rfl

/-- The category of perverse Weil sheaves on the affine line, the full subcategory of curve
perverse Weil complexes, is the heart of the perverse t-structure. -/
noncomputable instance : (curvePerverseTStructure (k₀ := k₀) (l := l)).Heart
    (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory where
  ι := ObjectProperty.ι _
  essImage_eq_heart := by
    ext K
    exact ⟨fun ⟨L, ⟨e⟩⟩ ↦ curvePerverse.prop_of_iso e L.property,
      fun hK ↦ ⟨⟨K, hK⟩, ⟨Iso.refl _⟩⟩⟩

/-- **Perverse Weil sheaves form an abelian category**: the curve perverse Weil complexes on the
affine line are the heart of the perverse t-structure, and the heart of a t-structure is abelian.
(blueprint: `lemma-perverse-weil-sheaves--1`) -/
noncomputable instance abelianCurvePerverse :
    Abelian (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory :=
  (curvePerverseTStructure (k₀ := k₀) (l := l)).abelianHeart _

end AffineLine

end WeilComplex

end AlgebraicGeometry
