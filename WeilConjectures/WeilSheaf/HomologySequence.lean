/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.WeilSheaf.Triangle

/-!
# The cohomology sequence of a distinguished triangle of Weil complexes

The cohomology sheaves `𝓗ⁿ` of Weil complexes form a homological functor: a distinguished
triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` gives exact sequences `𝓗ⁿK₁ ⟶ 𝓗ⁿK₂ ⟶ 𝓗ⁿK₃` of Weil sheaves
(`AlgebraicGeometry.WeilComplex.homologySheaf_exact₂`), and `𝓗ᵃ(K[m]) ≅ 𝓗ᵐ⁺ᵃK`
(`AlgebraicGeometry.WeilComplex.homologySheafShiftIso`).

From this we derive the dévissage principle behind the hypercohomology spectral sequence
`E₂^{a,b} = 𝓗ᵃΦ(𝓗ᵇK) ⇒ 𝓗ᵃ⁺ᵇΦ(K)` of a triangulated functor `Φ` of Weil complexes, in the form
in which it is used for weight bounds: if a family of properties `P n` of Weil sheaves is closed
under subobjects, quotients and extensions, and every `E₂`-term in total degree `n` satisfies
`P n`, then so does `𝓗ⁿΦ(K)` (`AlgebraicGeometry.WeilComplex.prop_homologySheaf_obj`). The
proof is by induction along the canonical truncation triangles `τ_{<b}K ⟶ K ⟶ τ_{≥b}K ⟶`, whose
third term is `𝓗ᵇK` placed in degree `b`.

## Main statements

- `AlgebraicGeometry.WeilComplex.homologySheaf_exact₂`: the cohomology sequence of a
  distinguished triangle is exact in the middle.
- `AlgebraicGeometry.WeilComplex.prop_homologySheaf_obj`: the dévissage along the
  hypercohomology spectral sequence of a triangulated functor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- A Weil complex is zero if its underlying object of the derived category is. -/
lemma isZero_of_isZero_obj {K : WeilComplex k₀ l X} (hK : IsZero K.obj) : IsZero K :=
  IsZero.of_full_of_faithful_of_isZero (WeilComplex.objectProperty k₀ l X).ι K hK

/-- A cohomology sheaf of a Weil complex is zero if the corresponding cohomology object of the
underlying object of the derived category is. -/
lemma isZero_homologySheaf_obj {K : WeilComplex k₀ l X} {n : ℤ}
    (hK : IsZero ((DerivedCategory.homologyFunctor _ n).obj K.obj)) :
    IsZero ((homologySheaf n).obj K) :=
  IsZero.of_full_of_faithful_of_isZero (WeilSheaf.objectProperty k₀ l X).ι _ hK

/-- The cohomology sheaves of a shifted Weil complex: `𝓗ᵃ(K[m]) ≅ 𝓗ᵃ'K` for `m + a = a'`. -/
noncomputable def homologySheafShiftIso (K : WeilComplex k₀ l X) (m a a' : ℤ) (h : m + a = a') :
    (homologySheaf a).obj (K⟦m⟧) ≅ (homologySheaf a').obj K :=
  ObjectProperty.isoMk _ ((DerivedCategory.homologyFunctor _ a).mapIso
    (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso m).app K) ≪≫
    ((DerivedCategory.homologyFunctor _ 0).shiftIso m a a' h).app K.obj)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The cohomology sequence `𝓗ⁿK₁ ⟶ 𝓗ⁿK₂ ⟶ 𝓗ⁿK₃` of a distinguished triangle
`K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of Weil complexes is exact
(blueprint: `lem-sp-long-exact-of-triangle`). -/
lemma homologySheaf_exact₂ (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (n : ℤ) :
    (ShortComplex.mk ((homologySheaf n).map T.mor₁) ((homologySheaf n).map T.mor₂)
      (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])).Exact := by
  let ι : WeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X := (WeilSheaf.objectProperty k₀ l X).ι
  have : PreservesFiniteLimits ι := inferInstanceAs
    (PreservesFiniteLimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι)
  have : PreservesFiniteColimits ι := inferInstanceAs
    (PreservesFiniteColimits (C := WeilSheaf k₀ l X) (WeilSheaf.objectProperty k₀ l X).ι)
  have : ι.Faithful := inferInstanceAs (WeilSheaf.objectProperty k₀ l X).ι.Faithful
  rw [← ShortComplex.exact_map_iff_of_faithful _ ι]
  exact DerivedCategory.HomologySequence.exact₂ _ hT n

/-- In a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of Weil complexes, `𝓗ⁿK₁ ⟶ 𝓗ⁿK₂` is an
isomorphism if `𝓗ⁿ⁻¹K₃` and `𝓗ⁿK₃` vanish. -/
lemma isIso_homologySheaf_map_mor₁ (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor _ n₀).obj T.obj₃.obj))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor _ n₁).obj T.obj₃.obj)) :
    IsIso ((homologySheaf n₁).map T.mor₁) := by
  have : IsIso ((WeilSheaf.objectProperty k₀ l X).ι.map ((homologySheaf n₁).map T.mor₁)) :=
    DerivedCategory.isIso_homologyMap_mor₁ _ hT n₀ n₁ h h₀ h₁
  exact isIso_of_fully_faithful (WeilSheaf.objectProperty k₀ l X).ι _

/-- In a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` of Weil complexes, `𝓗ⁿK₂ ⟶ 𝓗ⁿK₃` is an
isomorphism if `𝓗ⁿK₁` and `𝓗ⁿ⁺¹K₁` vanish. -/
lemma isIso_homologySheaf_map_mor₂ (T : Triangle (WeilComplex k₀ l X)) (hT : T ∈ distTriang _)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor _ n₀).obj T.obj₁.obj))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor _ n₁).obj T.obj₁.obj)) :
    IsIso ((homologySheaf n₀).map T.mor₂) := by
  have : IsIso ((WeilSheaf.objectProperty k₀ l X).ι.map ((homologySheaf n₀).map T.mor₂)) :=
    DerivedCategory.isIso_homologyMap_mor₂ _ hT n₀ n₁ h h₀ h₁
  exact isIso_of_fully_faithful (WeilSheaf.objectProperty k₀ l X).ι _

end

section Devissage

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (Φ : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  (Q : ℤ → ObjectProperty (WeilSheaf k₀ l X)) [∀ b, (Q b).IsClosedUnderIsomorphisms]
  (P : ℤ → ObjectProperty (WeilSheaf k₀ l Y)) [∀ n, (P n).IsClosedUnderIsomorphisms]
  [∀ n, (P n).IsClosedUnderSubobjects] [∀ n, (P n).IsClosedUnderQuotients]
  [∀ n, (P n).IsClosedUnderExtensions] [∀ n, (P n).ContainsZero]

/-- The induction of `AlgebraicGeometry.WeilComplex.prop_homologySheaf_obj`, on the length `N` of
the interval `[a, a + N - 1]` in which the cohomology of `K` is concentrated. -/
private lemma prop_homologySheaf_obj_aux
    (hQ : ∀ b (G : WeilSheaf k₀ l X), IsZero G → Q b G)
    (h : ∀ (a b : ℤ) (G : WeilSheaf k₀ l X), Q b G →
      P (a + b) ((homologySheaf a).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (N : ℕ) : ∀ (a : ℤ) (K : WeilComplex k₀ l X), K.obj.IsGE a → K.obj.IsLE (a + N - 1) →
      (∀ b, Q b ((homologySheaf b).obj K)) → ∀ n, P n ((homologySheaf n).obj (Φ.obj K)) := by
  induction N with
  | zero =>
    intro a K _ _ _ n
    have : K.obj.IsLE (a - 1) := by simpa using ‹K.obj.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK : IsZero K := isZero_of_isZero_obj
      (DerivedCategory.TStructure.t.isZero K.obj (a - 1) a (by lia))
    exact (P n).prop_of_isZero ((homologySheaf n).map_isZero (Φ.map_isZero hK))
  | succ N ih =>
    intro a K _ _ hK n
    set b : ℤ := a + N
    have : K.obj.IsLE b := DerivedCategory.TStructure.t.isLE_of_le K.obj (a + ↑(N + 1) - 1) _
      (by lia)
    let TD := (DerivedCategory.TStructure.t.triangleLTGE b).obj K.obj
    have hTD : TD ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLTGE_distinguished b K.obj
    -- the third term is a Weil complex, `𝓗ᵇK` placed in degree `b`
    have : TD.obj₃.IsLE b :=
      inferInstanceAs (DerivedCategory.TStructure.t.IsLE
        ((DerivedCategory.TStructure.t.truncGE b).obj K.obj) b)
    have : TD.obj₃.IsGE b := inferInstanceAs (DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE b).obj K.obj) b)
    have : TD.obj₁.IsGE a := inferInstanceAs (DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncLT b).obj K.obj) a)
    have : TD.obj₁.IsLE (b - 1) := inferInstanceAs (DerivedCategory.TStructure.t.IsLE
        ((DerivedCategory.TStructure.t.truncLT b).obj K.obj) (b - 1))
    have h₃ : WeilComplex.objectProperty k₀ l X TD.obj₃ :=
      ⟨⟨⟨b, inferInstance⟩, ⟨b, inferInstance⟩⟩, DerivedCategory.homologyProperty_truncGE K.2.2 b⟩
    have h₁ : WeilComplex.objectProperty k₀ l X TD.obj₁ :=
      (WeilComplex.objectProperty k₀ l X).ext_of_isTriangulatedClosed₁ _ hTD K.2 h₃
    obtain ⟨T, hT, -, -, -, ⟨e⟩⟩ :=
      (WeilComplex.objectProperty k₀ l X).exists_distTriang_ι_mapTriangle_iso TD hTD h₁ K.2 h₃
    -- transport the bounds along `e`
    let e₁ : TD.obj₁ ≅ T.obj₁.obj := (Triangle.π₁.mapIso e).symm
    let e₃ : TD.obj₃ ≅ T.obj₃.obj := (Triangle.π₃.mapIso e).symm
    have : T.obj₁.obj.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e₁ a
    have : T.obj₁.obj.IsLE (b - 1) := DerivedCategory.TStructure.t.isLE_of_iso e₁ (b - 1)
    have : T.obj₃.obj.IsGE b := DerivedCategory.TStructure.t.isGE_of_iso e₃ b
    have : T.obj₃.obj.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e₃ b
    let eK : T.obj₂ ≅ K := ObjectProperty.isoMk _ (Triangle.π₂.mapIso e)
    -- the cohomology of the first and of the third term
    have hQ₁ : ∀ q, Q q ((homologySheaf q).obj T.obj₁) := by
      intro q
      by_cases hq : q < b
      · have := isIso_homologySheaf_map_mor₁ T hT (q - 1) q (by lia)
          (DerivedCategory.isZero_of_isGE _ b _ (by lia))
          (DerivedCategory.isZero_of_isGE _ b _ (by lia))
        exact (Q q).prop_of_iso ((homologySheaf q).mapIso eK.symm ≪≫
          (asIso ((homologySheaf q).map T.mor₁)).symm) (hK q)
      · exact hQ q _ (isZero_homologySheaf_obj (DerivedCategory.isZero_of_isLE _ (b - 1) _
          (by lia)))
    have hP₁ : P n ((homologySheaf n).obj (Φ.obj T.obj₁)) :=
      ih a T.obj₁ inferInstance (DerivedCategory.TStructure.t.isLE_of_le _ (b - 1) _ (by lia))
        hQ₁ n
    obtain ⟨Y₃, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE T.obj₃.obj b
    let eH : (DerivedCategory.homologyFunctor _ b).obj T.obj₃.obj ≅ Y₃ :=
      (DerivedCategory.homologyFunctor _ b).mapIso eY ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app Y₃
    have hY : WeilSheaf.objectProperty k₀ l X Y₃ :=
      (WeilSheaf.objectProperty k₀ l X).prop_of_iso eH ((homologySheaf b).obj T.obj₃).property
    let G : WeilSheaf k₀ l X := ⟨Y₃, hY⟩
    have hG : Q b G := by
      have := isIso_homologySheaf_map_mor₂ T hT b (b + 1) rfl
        (DerivedCategory.isZero_of_isLE T.obj₁.obj (b - 1) b (sub_one_lt b))
        (DerivedCategory.isZero_of_isLE T.obj₁.obj (b - 1) (b + 1)
          ((sub_one_lt b).trans (lt_add_one b)))
      exact (Q b).prop_of_iso ((homologySheaf b).mapIso eK.symm ≪≫
        asIso ((homologySheaf b).map T.mor₂) ≪≫ ObjectProperty.isoMk _ eH) (hK b)
    let e₃' : T.obj₃ ≅ (WeilSheaf.toComplex.obj G)⟦-b⟧ :=
      (WeilComplex.objectProperty k₀ l X).fullyFaithfulι.preimageIso
        (eY ≪≫
          (((DerivedCategory.singleFunctors _).shiftIso (-b) b 0 (neg_add_cancel b)).app Y₃).symm ≪≫
          (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso (-b)).app
            (WeilSheaf.toComplex.obj G)).symm)
    have hP₃ : P n ((homologySheaf n).obj (Φ.obj T.obj₃)) := by
      have h' : P (n - b + b) _ := h (n - b) b G hG
      have hnb : n - b + b = n := sub_add_cancel n b
      rw [hnb] at h'
      exact (P n).prop_of_iso ((homologySheafShiftIso _ (-b) n (n - b) (neg_add_eq_sub b n)).symm ≪≫
        (homologySheaf n).mapIso ((Φ.commShiftIso (-b)).app _).symm ≪≫
        (homologySheaf n).mapIso (Φ.mapIso e₃').symm) h'
    have hP₂ := (P n).prop_X₂_of_exact_of_isClosedUnderExtensions
      (homologySheaf_exact₂ _ (Φ.map_distinguished T hT) n) hP₁ hP₃
    exact (P n).prop_of_iso ((homologySheaf n).mapIso (Φ.mapIso eK)) hP₂

/-- **Dévissage along the hypercohomology spectral sequence.** Let `Φ` be a triangulated functor
of Weil complexes, and let `P n` be properties of Weil sheaves, each closed under subobjects,
quotients and extensions. Let `K` be a Weil complex whose cohomology sheaves `𝓗ᵇK` satisfy
properties `Q b` such that every `E₂`-term `𝓗ᵃΦ(G)` with `Q b G` satisfies `P (a + b)`. Then
`𝓗ⁿΦ(K)` satisfies `P n`: it is filtered by subquotients of the `E₂`-terms of total degree `n`
of the spectral sequence `E₂^{a,b} = 𝓗ᵃΦ(𝓗ᵇK) ⇒ 𝓗ᵃ⁺ᵇΦ(K)`
(blueprint: `def-weil-pbc-hypercohomology-filtrations`,
`lemma-weil-pbc-hypercohomology-convergence`). The properties `Q b` must hold for zero sheaves,
which the truncations of `K` have as cohomology sheaves outside their range. -/
theorem prop_homologySheaf_obj
    (hQ : ∀ b (G : WeilSheaf k₀ l X), IsZero G → Q b G)
    (h : ∀ (a b : ℤ) (G : WeilSheaf k₀ l X), Q b G →
      P (a + b) ((homologySheaf a).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (K : WeilComplex k₀ l X) (hK : ∀ b, Q b ((homologySheaf b).obj K)) (n : ℤ) :
    P n ((homologySheaf n).obj (Φ.obj K)) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := K.2.1
  have : K.obj.IsGE a := ha
  have : K.obj.IsLE b := hb
  exact prop_homologySheaf_obj_aux Φ Q P hQ h (b - a + 1).toNat a K inferInstance
    (DerivedCategory.TStructure.t.isLE_of_le K.obj b _ (by lia)) hK n

end Devissage

end WeilComplex

end AlgebraicGeometry
