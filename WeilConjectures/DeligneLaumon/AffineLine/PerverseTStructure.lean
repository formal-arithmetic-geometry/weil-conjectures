/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.CurvePunctualPart
public import WeilConjectures.DeligneLaumon.AffineLine.Perverse
public import WeilConjectures.DeligneLaumon.Reduction.FibreCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# The perverse t-structure on a smooth curve

On a smooth curve `C` over the finite field `k₀`, the classes `ᵖD^{≤0}`
(`AlgebraicGeometry.WeilComplex.IsCurvePerverseUpper`) and `ᵖD^{≥0}`
(`AlgebraicGeometry.WeilComplex.IsCurvePerverseLower`) form a bounded t-structure on the Weil
complexes on `C`, whose heart, the category of perverse sheaves on `C`, is abelian
(blueprint `lemma-perverse-sheaves-curve--1`).

The orthogonality axiom is
`AlgebraicGeometry.WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero`. The truncation
triangle of a Weil complex `K` is built from the standard truncation
`τ_{<0} K ⟶ K ⟶ τ_{≥0} K ⟶` and the maximal punctual subsheaf `P` of `𝓗⁰K`: the cone `Y`
of `P[0] ⟶ τ_{≥0} K` lies in `ᵖD^{≥1}`, and the fibre of the composite `K ⟶ τ_{≥0} K ⟶ Y`
lies in `ᵖD^{≤0}`. The abelianness of the heart is the general fact
`CategoryTheory.Triangulated.TStructure.abelianHeart`.

The only sheaf-theoretic input is the existence of the maximal punctual subsheaf of a Weil sheaf,
`AlgebraicGeometry.WeilSheaf.exists_mono_support_finite_cokernel`: it is the kernel of the unit
`F ⟶ j_* j^* F` of a dense open on which `F` is lisse.

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsCurvePerverseGE`: the shifted lower classes `ᵖD^{≥n}`.
- `AlgebraicGeometry.WeilComplex.exists_tStructure_of_punctual`: the curve perverse classes form
  a bounded t-structure with abelian heart, given maximal punctual subsheaves.
- `AlgebraicGeometry.WeilComplex.exists_curvePerverse_tStructure`: the clause
  `lemma-perverse-sheaves-curve--1` on a smooth curve.
- `AlgebraicGeometry.WeilComplex.exists_curvePerverse_tStructure_affineLine`: the same clause on
  the affine line.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated Triangulated

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The shifted lower class `ᵖD^{≥n} = ᵖD^{≥0}[-n]` of the perverse t-structure on a smooth
curve: `𝓗ᵃK = 0` for `a < n - 1`, and `𝓗ⁿ⁻¹K` has no nonzero subsheaf of finite support.
(blueprint: `lemma-perverse-sheaves-curve--1`) -/
def IsCurvePerverseGE (n : ℤ) (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < n - 1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (n - 1)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

theorem isCurvePerverseGE_zero_iff (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseGE 0 ↔ K.IsCurvePerverseLower :=
  Iff.rfl

theorem IsCurvePerverseGE.of_iso {n : ℤ} {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (hK : K.IsCurvePerverseGE n) : L.IsCurvePerverseGE n :=
  ⟨fun a ha ↦ (hK.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
    fun G i _ hG ↦ hK.2 G (i ≫ (homologySheaf (n - 1)).map e.inv) inferInstance hG⟩

/-- The shifted classes `ᵖD^{≥n}` are compatible with the shift: `K[m] ∈ ᵖD^{≥n'}` for
`K ∈ ᵖD^{≥n}` and `m + n' = n`. -/
theorem IsCurvePerverseGE.shift {n : ℤ} {K : WeilComplex k₀ l X} (hK : K.IsCurvePerverseGE n)
    (m n' : ℤ) (h : m + n' = n) : (K⟦m⟧).IsCurvePerverseGE n' :=
  ⟨fun a ha ↦ (hK.1 (m + a) (by omega)).of_iso (homologySheafShiftIso K m a (m + a) rfl),
    fun G i _ hG ↦ hK.2 G (i ≫ (homologySheafShiftIso K m (n' - 1) (n - 1) (by omega)).hom)
      inferInstance hG⟩

theorem isCurvePerverseGE_iff_isCurvePerverseLower_shift (n : ℤ) (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseGE n ↔ (K⟦n⟧).IsCurvePerverseLower := by
  rw [← isCurvePerverseGE_zero_iff]
  refine ⟨fun h ↦ h.shift n 0 (by omega), fun h ↦ ?_⟩
  exact (h.shift (-n) n (by omega)).of_iso ((shiftFunctorCompIsoId _ n (-n) (by omega)).app K)

theorem IsCurvePerverseLE.isCurvePerverseLE_add_one {n : ℤ} {K : WeilComplex k₀ l X}
    (hK : K.IsCurvePerverseLE n) : K.IsCurvePerverseLE (n + 1) := by
  refine ⟨fun a ha ↦ hK.1 a (by omega), ?_⟩
  rw [WeilSheaf.support_eq_empty_of_isZero (hK.1 (n + 1) (by omega))]
  exact Set.finite_empty

theorem IsCurvePerverseGE.isCurvePerverseGE_sub_one {n : ℤ} {K : WeilComplex k₀ l X}
    (hK : K.IsCurvePerverseGE n) : K.IsCurvePerverseGE (n - 1) :=
  ⟨fun a ha ↦ hK.1 a (by omega), fun _ i _ _ ↦ IsZero.of_mono i (hK.1 _ (by omega))⟩

/-- A Weil complex is bounded for the curve perverse classes: it lies in `ᵖD^{≥a} ∩ ᵖD^{≤b}`
for some `a` and `b`. -/
theorem exists_isCurvePerverseGE_isCurvePerverseLE (K : WeilComplex k₀ l X) :
    ∃ a b : ℤ, K.IsCurvePerverseGE a ∧ K.IsCurvePerverseLE b := by
  obtain ⟨⟨m, hm⟩, ⟨M, hM⟩⟩ := K.property.1
  have hge (a : ℤ) (ha : a < m) : IsZero ((homologySheaf a).obj K) :=
    (isZero_homologySheaf_obj_iff a K).2 ((_root_.DerivedCategory.isGE_iff _ m).1 hm a ha)
  have hle (a : ℤ) (ha : M < a) : IsZero ((homologySheaf a).obj K) :=
    (isZero_homologySheaf_obj_iff a K).2 ((_root_.DerivedCategory.isLE_iff _ M).1 hM a ha)
  refine ⟨m, M + 1, ⟨fun a ha ↦ hge a (by omega), fun _ i _ _ ↦
    IsZero.of_mono i (hge _ (by omega))⟩, fun a ha ↦ hle a (by omega), ?_⟩
  rw [WeilSheaf.support_eq_empty_of_isZero (hle (M + 1) (by omega))]
  exact Set.finite_empty

section Triangle

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶`, the map `𝓗ᵃT₂ ⟶ 𝓗ᵃT₃` is an epimorphism when
`𝓗ᵃ⁺¹T₁ = 0`. -/
theorem epi_homologySheaf_map_mor₂ (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (a : ℤ) (h : IsZero ((homologySheaf (a + 1)).obj T.obj₁)) :
    Epi ((homologySheaf a).map T.mor₂) :=
  (homologySheaf_exact₃ T a (a + 1) hT rfl).epi_f (h.eq_of_tgt _ _)

/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶`, the map `𝓗ᵃT₂ ⟶ 𝓗ᵃT₃` is a monomorphism when
`𝓗ᵃT₁ = 0`. -/
theorem mono_homologySheaf_map_mor₂ (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (a : ℤ) (h : IsZero ((homologySheaf a).obj T.obj₁)) :
    Mono ((homologySheaf a).map T.mor₂) :=
  (homologySheaf_exact₂ T a hT).mono_g (h.eq_of_src _ _)

/-- **Perverse truncation on a smooth curve** (`lemma-perverse-sheaves-curve--1`): if every
Weil sheaf `F` on `X` has a punctual subsheaf `P` such that `F / P` has no nonzero punctual
subsheaf, then every Weil complex `K` sits in a distinguished triangle `A ⟶ K ⟶ B ⟶ A[1]` with
`A ∈ ᵖD^{≤0}` and `B ∈ ᵖD^{≥1}`. With `P ⊆ 𝓗⁰K` maximal punctual, `B` is the cone of
`P[0] ⟶ τ_{≥0} K` and `A` the fibre of `K ⟶ B`. -/
theorem exists_distTriang_isCurvePerverseLE_isCurvePerverseGE
    (hX : ∀ F : WeilSheaf k₀ l X, ∃ (P : WeilSheaf k₀ l X) (i : P ⟶ F), Mono i ∧
      P.support.Finite ∧ ∀ (G : WeilSheaf k₀ l X) (j : G ⟶ cokernel i), Mono j →
        G.support.Finite → IsZero G)
    (K : WeilComplex k₀ l X) :
    ∃ (A B : WeilComplex k₀ l X) (_ : A.IsCurvePerverseLE 0) (_ : B.IsCurvePerverseGE 1)
      (f : A ⟶ K) (g : K ⟶ B) (h : B ⟶ A⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang _ := by
  obtain ⟨K₁, Z, f₁, g₁, h₁, hT₁, hK₁, hZ, -, -⟩ := exists_distTriang_truncLT K 0
  set T₁ := Triangle.mk f₁ g₁ h₁
  have hK₁z (a : ℤ) (ha : 0 ≤ a) : IsZero ((homologySheaf a).obj K₁) :=
    (isZero_homologySheaf_obj_iff a K₁).2
      ((_root_.DerivedCategory.isLE_iff _ (0 - 1)).1 hK₁ a (by omega))
  have hZz (a : ℤ) (ha : a < 0) : IsZero ((homologySheaf a).obj Z) :=
    (isZero_homologySheaf_obj_iff a Z).2 ((_root_.DerivedCategory.isGE_iff _ 0).1 hZ a ha)
  obtain ⟨P, i, _, hPf, hQ⟩ := hX ((homologySheaf 0).obj Z)
  set P₀ := WeilSheaf.toComplex.obj P
  have hP₀z (a : ℤ) (ha : a ≠ 0) : IsZero ((homologySheaf a).obj P₀) :=
    isZero_homologySheaf_singleComplex ha P
  let e : (homologySheaf 0).obj P₀ ≅ P := WeilSheaf.toComplexCompHomologySheafIso.app P
  obtain ⟨φ, hφ⟩ := (homologySheaf_map_bijective 0 (K := P₀) (L := Z)
    (fun a ha ↦ hP₀z a ha.ne') hZz).2 (e.hom ≫ i)
  simp only at hφ
  obtain ⟨Y, ψ, δ, hT₂⟩ := distinguished_cocone_triangle φ
  set T₂ := Triangle.mk φ ψ δ
  obtain ⟨W, u, v, hT₃⟩ := distinguished_cocone_triangle (g₁ ≫ ψ)
  have hT := inv_rot_of_distTriang _ hT₃
  set T := (Triangle.mk (g₁ ≫ ψ) u v).invRotate
  -- the cohomology of `g₁ : K ⟶ τ_{≥0} K` and of `ψ : τ_{≥0} K ⟶ Y`
  have hg₁e (a : ℤ) (ha : 0 ≤ a) : Epi ((homologySheaf a).map g₁) :=
    epi_homologySheaf_map_mor₂ T₁ hT₁ a (hK₁z (a + 1) (by omega))
  have hg₁m (a : ℤ) (ha : 0 ≤ a) : Mono ((homologySheaf a).map g₁) :=
    mono_homologySheaf_map_mor₂ T₁ hT₁ a (hK₁z a ha)
  have hψe (a : ℤ) (ha : 0 ≤ a) : Epi ((homologySheaf a).map ψ) :=
    epi_homologySheaf_map_mor₂ T₂ hT₂ a (hP₀z (a + 1) (by omega))
  have hψm (a : ℤ) (ha : 1 ≤ a) : Mono ((homologySheaf a).map ψ) :=
    mono_homologySheaf_map_mor₂ T₂ hT₂ a (hP₀z a (by omega))
  have hgψe (a : ℤ) (ha : 0 ≤ a) : Epi ((homologySheaf a).map (g₁ ≫ ψ)) := by
    have := hg₁e a ha
    have := hψe a ha
    rw [Functor.map_comp]
    exact epi_comp _ _
  have hgψm (a : ℤ) (ha : 1 ≤ a) : Mono ((homologySheaf a).map (g₁ ≫ ψ)) := by
    have := hg₁m a (by omega)
    have := hψm a ha
    rw [Functor.map_comp]
    exact mono_comp _ _
  -- `𝓗ᵃY = 0` for `a < 0`
  have hYm1 : IsZero ((homologySheaf (-1)).obj Y) := by
    refine (homologySheaf_exact₃ T₂ (-1) 0 hT₂ (by norm_num)).isZero_X₂
      ((hZz (-1) (by norm_num)).eq_of_src _ _) ?_
    refine (homologySheaf_exact₁ T₂ (-1) 0 hT₂ (by norm_num)).mono_g_iff.1 ?_
    change Mono ((homologySheaf 0).map φ)
    rw [hφ]
    exact mono_comp _ _
  have hYz (a : ℤ) (ha : a < 0) : IsZero ((homologySheaf a).obj Y) := by
    obtain ha | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
    · exact (homologySheaf_exact₃ T₂ a (a + 1) hT₂ rfl).isZero_X₂
        ((hZz a (by omega)).eq_of_src _ _) ((hP₀z (a + 1) (by omega)).eq_of_tgt _ _)
    · exact hYm1
  -- `𝓗⁰Y` is the cokernel of `P ⟶ 𝓗⁰(τ_{≥0} K)`
  let S := ShortComplex.mk ((homologySheaf 0).map φ) ((homologySheaf 0).map ψ)
    (by rw [← Functor.map_comp, show φ ≫ ψ = 0 from comp_distTriang_mor_zero₁₂ _ hT₂,
      Functor.map_zero])
  have hS : S.Exact := homologySheaf_exact₂ T₂ 0 hT₂
  have : Epi ((homologySheaf 0).map ψ) := hψe 0 le_rfl
  let E : (homologySheaf 0).obj Y ≅ cokernel i :=
    IsColimit.coconePointUniqueUpToIso (hS.gIsCokernel)
      (cokernelIsCokernel ((homologySheaf 0).map φ)) ≪≫ cokernelIsoOfEq hφ ≪≫
        cokernelEpiComp e.hom i
  have hYGE : Y.IsCurvePerverseGE 1 :=
    ⟨fun a ha ↦ hYz a (by omega), fun G j _ hG ↦ hQ G (j ≫ E.hom) inferInstance hG⟩
  -- `𝓗ᵃ` of the fibre `T.obj₁` of `K ⟶ Y`
  have hXz (a : ℤ) (ha : 1 ≤ a) : IsZero ((homologySheaf a).obj T.obj₁) := by
    refine (homologySheaf_exact₁ T (a - 1) a hT (by omega)).isZero_X₂ ?_ ?_
    · have := hgψe (a - 1) (by omega)
      exact (homologySheaf_exact₃ T (a - 1) a hT (by omega)).epi_f_iff.1 this
    · have := hgψm a ha
      exact (homologySheaf_exact₂ T a hT).mono_g_iff.1 this
  have hXm : Mono ((homologySheaf 0).map T.mor₁) :=
    (homologySheaf_exact₁ T (-1) 0 hT (by norm_num)).mono_g (hYm1.eq_of_src _ _)
  -- `𝓗⁰` of the fibre embeds into the kernel of `𝓗⁰ψ`, a quotient of `P`
  have hXf : ((homologySheaf 0).obj T.obj₁).support.Finite := by
    have : Mono ((homologySheaf 0).map g₁) := hg₁m 0 le_rfl
    have hw : ((homologySheaf 0).map T.mor₁ ≫ (homologySheaf 0).map g₁) ≫
        (homologySheaf 0).map ψ = 0 := by
      rw [Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        show T.mor₁ ≫ g₁ ≫ ψ = 0 from comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero]
    have : Mono (kernel.lift _ _ hw) := mono_of_mono_fac (kernel.lift_ι _ _ hw)
    have : Epi (kernel.lift _ _ S.zero) := hS.epi_kernelLift
    refine (hPf.subset ?_).subset (WeilSheaf.support_subset_of_mono (kernel.lift _ _ hw))
    rw [← WeilSheaf.support_congr e]
    exact WeilSheaf.support_subset_of_epi (kernel.lift _ _ S.zero)
  exact ⟨T.obj₁, Y, ⟨fun a ha ↦ hXz a ha, hXf⟩, hYGE, _, g₁ ≫ ψ, _, hT⟩

end Triangle

section TStructure

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]

/-- Morphisms from `ᵖD^{≤0}` to `ᵖD^{≥1}` vanish on a smooth curve: after the shift by `1`
this is `AlgebraicGeometry.WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero`. -/
theorem hom_eq_zero_of_isCurvePerverseLE_of_isCurvePerverseGE {K L : WeilComplex k₀ l X}
    (hK : K.IsCurvePerverseLE 0) (hL : L.IsCurvePerverseGE 1) (f : K ⟶ L) : f = 0 := by
  apply (shiftFunctor (WeilComplex k₀ l X) (1 : ℤ)).map_injective
  rw [Functor.map_zero]
  exact (isCurvePerverseLower_iff_forall_hom_eq_zero (L⟦(1 : ℤ)⟧)).1
    ((isCurvePerverseGE_zero_iff _).1 (hL.shift 1 0 (by norm_num))) _
    (hK.shift 1 (-1) (by norm_num)) _

/-- **The perverse t-structure on a smooth curve** (blueprint `lemma-perverse-sheaves-curve--1`),
given the existence of maximal punctual subsheaves: there is a t-structure on the Weil complexes
whose classes `≤ n` and `≥ n` are `ᵖD^{≤n}` and `ᵖD^{≥n} = ᵖD^{≥0}[-n]`; it is bounded, its
heart is the class of curve perverse complexes, and the heart is abelian. -/
theorem exists_tStructure_of_punctual
    (hX : ∀ F : WeilSheaf k₀ l X, ∃ (P : WeilSheaf k₀ l X) (i : P ⟶ F), Mono i ∧
      P.support.Finite ∧ ∀ (G : WeilSheaf k₀ l X) (j : G ⟶ cokernel i), Mono j →
        G.support.Finite → IsZero G) :
    ∃ t : TStructure (WeilComplex k₀ l X),
      t.le 0 = IsCurvePerverseUpper ∧ t.ge 0 = IsCurvePerverseLower ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l X), t.le n K ↔ K.IsCurvePerverseLE n) ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l X), t.ge n K ↔ (K⟦n⟧).IsCurvePerverseLower) ∧
      (∀ K : WeilComplex k₀ l X, ∃ a b : ℤ, t.ge a K ∧ t.le b K) ∧
      t.heart = IsCurvePerverse ∧
      ∃ h : Abelian t.heart.FullSubcategory,
        h.toPreadditive = (inferInstance : Preadditive t.heart.FullSubcategory) := by
  let t : TStructure (WeilComplex k₀ l X) :=
    { le n := IsCurvePerverseLE n
      ge n := IsCurvePerverseGE n
      le_isClosedUnderIsomorphisms n := ⟨fun e h ↦ h.of_iso e⟩
      ge_isClosedUnderIsomorphisms n := ⟨fun e h ↦ h.of_iso e⟩
      le_shift n a n' h K hK := hK.shift a n' h
      ge_shift n a n' h K hK := hK.shift a n' h
      zero' _ _ f hK hL := hom_eq_zero_of_isCurvePerverseLE_of_isCurvePerverseGE hK hL f
      le_zero_le _ hK := hK.isCurvePerverseLE_add_one
      ge_one_le _ hK := hK.isCurvePerverseGE_sub_one
      exists_triangle_zero_one K := exists_distTriang_isCurvePerverseLE_isCurvePerverseGE hX K }
  have hge0 : t.ge 0 = IsCurvePerverseLower := by
    ext K
    exact isCurvePerverseGE_zero_iff K
  refine ⟨t, rfl, hge0, fun _ _ ↦ Iff.rfl,
    fun n K ↦ isCurvePerverseGE_iff_isCurvePerverseLower_shift n K,
    exists_isCurvePerverseGE_isCurvePerverseLE, ?_,
    letI := t.hasHeartFullSubcategory; ⟨t.abelianHeart _, rfl⟩⟩
  change t.le 0 ⊓ t.ge 0 = _
  rw [hge0]
  rfl

end TStructure

end WeilComplex

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

attribute [local instance 1000] IsSeparated.isSeparated_of_mono in
/-- **Maximal punctual subsheaves on the affine line**: for a dense open `j : U₀ ↪ 𝔸¹` on which
`F` is lisse, the kernel `P` of the unit `F ⟶ j_* j^* F` is punctual, and `F / P` embeds into
`j_* j^* F`, which has no nonzero punctual subsheaf. -/
theorem exists_mono_support_finite_cokernel_affineLine (F : WeilSheaf k₀ l (affineLine k₀)) :
    ∃ (P : WeilSheaf k₀ l (affineLine k₀)) (i : P ⟶ F), Mono i ∧ P.support.Finite ∧
      ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (j : G ⟶ cokernel i), Mono j →
        G.support.Finite → IsZero G := by
  have : IsNoetherian (affineLine k₀) :=
    isNoetherian_of_locallyOfFiniteType (affineLine k₀ ↘ Spec (.of k₀))
  obtain ⟨U, hU, hUl⟩ := exists_dense_isLisse_upperStar F
  have : IsDominant U.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  set η := (upperStarLowerStarAdjunction (k₀ := k₀) (l := l) U.ι).unit.app F
  refine ⟨kernel η, kernel.ι η, inferInstance, support_finite_kernel_unit_app U.ι F,
    fun G j _ hG ↦ ?_⟩
  have : Mono (Abelian.factorThruCoimage η) := inferInstance
  exact IsZero.of_mono_eq_zero j ((cancel_mono (Abelian.factorThruCoimage η)).1
    ((eq_zero_of_support_finite_lowerStar U.ι hUl hG _).trans zero_comp.symm))

end WeilSheaf

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The perverse t-structure on a smooth curve** (blueprint `lemma-perverse-sheaves-curve--1`):
on a smooth curve `X` over `k₀`, the classes `ᵖD^{≤0}` and `ᵖD^{≥0}` form a bounded t-structure
on the Weil complexes, with `≤ n` and `≥ n` parts their shifts, and its heart, the category of
perverse sheaves on `X`, is abelian. -/
theorem exists_curvePerverse_tStructure {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] :
    ∃ t : TStructure (WeilComplex k₀ l X),
      t.le 0 = IsCurvePerverseUpper ∧ t.ge 0 = IsCurvePerverseLower ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l X), t.le n K ↔ K.IsCurvePerverseLE n) ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l X), t.ge n K ↔ (K⟦n⟧).IsCurvePerverseLower) ∧
      (∀ K : WeilComplex k₀ l X, ∃ a b : ℤ, t.ge a K ∧ t.le b K) ∧
      t.heart = IsCurvePerverse ∧
      ∃ h : Abelian t.heart.FullSubcategory,
        h.toPreadditive = (inferInstance : Preadditive t.heart.FullSubcategory) :=
  exists_tStructure_of_punctual WeilSheaf.exists_mono_support_finite_cokernel

/-- **The perverse t-structure on the affine line** (blueprint `lemma-perverse-sheaves-curve--1`):
the classes `ᵖD^{≤0}` and `ᵖD^{≥0}` form a bounded t-structure on the Weil complexes on `𝔸¹`,
with `≤ n` and `≥ n` parts their shifts, whose heart `curvePerverse` is abelian. -/
theorem exists_curvePerverse_tStructure_affineLine :
    ∃ t : TStructure (WeilComplex k₀ l (affineLine k₀)),
      t.le 0 = IsCurvePerverseUpper ∧ t.ge 0 = IsCurvePerverseLower ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l (affineLine k₀)), t.le n K ↔ K.IsCurvePerverseLE n) ∧
      (∀ (n : ℤ) (K : WeilComplex k₀ l (affineLine k₀)),
        t.ge n K ↔ (K⟦n⟧).IsCurvePerverseLower) ∧
      (∀ K : WeilComplex k₀ l (affineLine k₀), ∃ a b : ℤ, t.ge a K ∧ t.le b K) ∧
      t.heart = curvePerverse ∧
      ∃ h : Abelian t.heart.FullSubcategory,
        h.toPreadditive = (inferInstance : Preadditive t.heart.FullSubcategory) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  exact exists_tStructure_of_punctual WeilSheaf.exists_mono_support_finite_cokernel_affineLine

end WeilComplex

end AlgebraicGeometry
