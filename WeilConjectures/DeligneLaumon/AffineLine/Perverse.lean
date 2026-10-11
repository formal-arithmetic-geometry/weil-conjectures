/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.SupportUpperStar
public import WeilConjectures.WeilSheaf.HomologyShift
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseDenseOpen
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Irreducible

/-!
# The curve perverse t-structure and Fourier exactness

On a smooth curve the two classes of the perverse t-structure are described purely in terms of
the ordinary cohomology sheaves of a complex: the *upper* class consists of the complexes `K`
with `𝓗ᵃK = 0` for `a > 0` and `𝓗⁰K` of finite support, the *lower* class of those with
`𝓗ᵃK = 0` for `a < -1` and `𝓗⁻¹K` without a nonzero finite-support subsheaf. Their
intersection is the perverse heart. The Fourier–Deligne transform of the affine line is an
exact equivalence between the perverse hearts of the two dual lines.

The three classes below are stated for an arbitrary `k₀`-scheme, but they agree with the
perverse t-structure only on a smooth curve — whence the names. On a scheme of dimension at
least two the perverse t-structure is not described by these two conditions, and the names
`IsCurvePerverse*` keep the description distinct from the genuine t-structure that
`sec-six-functors` will build.

That the Fourier transform is an equivalence at all is Fourier inversion, which belongs to the
block `sec-fourier-transform`: it is `AlgebraicGeometry.isEquivalence_fourierTransform`. What
this subsection adds is that the equivalence is exact for the perverse t-structures.

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsCurvePerverseUpper`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverseLower`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverse`: the two truncation classes on a curve and
  the perverse heart.
- `AlgebraicGeometry.WeilComplex.IsCurvePerverseLE`: the shifted upper classes `ᵖD^{≤n}`.
- `AlgebraicGeometry.WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero`: on a smooth
  curve the lower class is the right orthogonal of `ᵖD^{≤-1}`, the t-structure axiom of
  `thm-a1-curve-perverse-heart`.
- `AlgebraicGeometry.WeilComplex.simple_iff`: the simple curve perverse sheaves on the affine
  line (`prop-a1-curve-perverse-simples`), and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.simple_middleExtension`: the middle extension of
  an irreducible lisse sheaf is simple.
- `AlgebraicGeometry.isCurvePerverseLE_fourierTransform_obj`,
  `AlgebraicGeometry.isCurvePerverseLE_fourierTransform_inv_obj`: `FT_ψ` and its inverse
  preserve the upper classes (`thm-a1-fourier-t-exact`).
- `AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`: `FT_ψ` preserves and reflects
  perversity.
- `AlgebraicGeometry.simple_fourierTransform_obj`: `FT_ψ` preserves simple perverse objects.

## Implementation notes

The blueprint defines `ᵖD^{≤0}` and `ᵖD^{≥0}` by the support and cosupport conditions, and
proves in `thm-a1-curve-perverse-heart` that on a smooth curve they are the upper and lower
classes above. The support and cosupport conditions are formalised on the étale site, in
`WeilConjectures.SixFunctors.Etale.Perverse.Basic`; for Weil complexes, which have no Verdier
dual yet, the curve classes are taken as the definition, and parts (1) and (3) of the theorem
hold by definition. Part (5), on short exact sequences in the heart, is not stated: the
provisional `AlgebraicGeometry.WeilComplex` is not triangulated, so its curve perverse heart
carries no abelian structure.

Following the blueprint, the lower class is reached through orthogonality: `FT_ψ` and its
inverse preserve the upper classes, hence `FT_ψ` preserves their right orthogonals.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The upper truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a > 0`, and `𝓗⁰K` has finite support. (blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverseUpper (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, 0 < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf (0 : ℤ)).obj K)).Finite

/-- The lower truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a < -1`, and `𝓗⁻¹K` has no nonzero subsheaf of finite support.
(blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverseLower (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (-1 : ℤ)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

/-- A Weil complex on a smooth curve is *curve perverse* if it lies in both truncation classes.
(blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverse (K : WeilComplex k₀ l X) : Prop :=
  K.IsCurvePerverseUpper ∧ K.IsCurvePerverseLower

/-- The shifted upper class `ᵖD^{≤n} = ᵖD^{≤0}[-n]` of the perverse t-structure on a smooth
curve: `𝓗ᵃK = 0` for `a > n`, and `𝓗ⁿK` has finite support.
(blueprint: `thm-a1-curve-perverse-heart`) -/
def IsCurvePerverseLE (n : ℤ) (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, n < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf n).obj K)).Finite

theorem isCurvePerverseUpper_iff_isCurvePerverseLE_zero (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseUpper ↔ K.IsCurvePerverseLE 0 :=
  Iff.rfl

/-- Curve perversity is invariant under isomorphism: the cohomology sheaves of isomorphic
complexes are isomorphic, hence have the same support. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)) where
  of_iso {K K'} e h := by
    refine ⟨⟨fun a ha ↦ (h.1.1 a ha).of_iso ((homologySheaf a).mapIso e).symm, ?_⟩,
      ⟨fun a ha ↦ (h.2.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
        fun G i _ hG ↦ h.2.2 G (i ≫ (homologySheaf (-1 : ℤ)).map e.inv) inferInstance hG⟩⟩
    rw [← WeilSheaf.support_congr ((homologySheaf (0 : ℤ)).mapIso e)]
    exact h.1.2

theorem IsCurvePerverseLE.of_iso {n : ℤ} {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (hK : K.IsCurvePerverseLE n) : L.IsCurvePerverseLE n :=
  ⟨fun a ha ↦ (hK.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
    WeilSheaf.support_congr ((homologySheaf n).mapIso e) ▸ hK.2⟩

section Curve

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **The perverse t-structure on a smooth curve**, orthogonality: on a smooth curve
`C` of finite type over `k₀`, a Weil complex lies in the lower class `ᵖD^{≥0}` exactly when it
receives no nonzero morphism from an object of `ᵖD^{≤-1}`. Together with the truncation
triangles this is the statement that the two curve classes form a t-structure.
(blueprint: `thm-a1-curve-perverse-heart`) -/
theorem isCurvePerverseLower_iff_forall_hom_eq_zero (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseLower ↔
      ∀ M : WeilComplex k₀ l X, M.IsCurvePerverseLE (-1) → ∀ f : M ⟶ K, f = 0 := by
  have : Smooth (X ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  constructor
  · rintro ⟨h1, h2⟩ M ⟨hM1, hM2⟩ f
    have : K.obj.IsGE (-1) := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (h1 i hi)
    have : M.obj.IsLE (-1) := (_root_.DerivedCategory.isLE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i M).1 (hM1 i hi)
    have hg : (homologySheaf (-1)).map f = 0 := by
      set g := (homologySheaf (-1)).map f
      have hI := h2 (Limits.image g) (Limits.image.ι g) inferInstance
        (hM2.subset (WeilSheaf.support_subset_of_epi (Limits.factorThruImage g)))
      rw [← Limits.image.fac g, hI.eq_of_src (Limits.image.ι g) 0, Limits.comp_zero]
    apply ObjectProperty.hom_ext
    apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE (-1)).1
    exact (congrArg (fun φ ↦ φ.hom) hg).trans (Functor.map_zero _ _ _).symm
  · intro H
    have key (a : ℤ) [K.obj.IsGE a] (G : WeilSheaf k₀ l X)
        (hG : (singleComplex a G).IsCurvePerverseLE (-1)) (i : G ⟶ (homologySheaf a).obj K) :
        i = 0 := by
      have : (singleComplex a G).obj.IsLE a :=
        inferInstanceAs (_root_.DerivedCategory.IsLE
          ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)
      obtain ⟨f, hf⟩ := (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
        (X := (singleComplex a G).obj) (Y := K.obj) a).2
        ((homologySheafSingleComplexIso a G).hom.hom ≫ i.hom)
      have hf0 : f = 0 := congrArg (fun φ ↦ φ.hom) (H _ hG (ObjectProperty.homMk f))
      simp only [hf0, Functor.map_zero] at hf
      apply ObjectProperty.hom_ext
      rw [← cancel_epi (homologySheafSingleComplexIso a G).hom.hom, ← hf]
      exact (Limits.comp_zero).symm
    have hLE (a : ℤ) (ha : a < -1) (G : WeilSheaf k₀ l X) :
        (singleComplex a G).IsCurvePerverseLE (-1) :=
      ⟨fun b hb ↦ isZero_homologySheaf_singleComplex (by omega) G, by
        rw [WeilSheaf.support_eq_empty_of_isZero
          (isZero_homologySheaf_singleComplex (by omega) G)]
        exact Set.finite_empty⟩
    have h1 : ∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K) := by
      by_contra! hcon
      obtain ⟨⟨m, hm⟩, -⟩ := K.property.1
      obtain ⟨a, ⟨ha, hza⟩, hmin⟩ := Int.exists_least_of_bdd
        (P := fun a ↦ a < -1 ∧ ¬ IsZero ((homologySheaf a).obj K))
        ⟨m, fun z ⟨_, hz⟩ ↦ by
          by_contra! hzm
          exact hz ((isZero_homologySheaf_obj_iff z K).2
            ((_root_.DerivedCategory.isGE_iff _ m).1 hm z hzm))⟩ hcon
      have : K.obj.IsGE a := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦ by
        by_contra hi'
        have := hmin i ⟨by omega, fun h ↦ hi' ((isZero_homologySheaf_obj_iff i K).1 h)⟩
        omega
      apply hza
      rw [IsZero.iff_id_eq_zero]
      exact key a _ (hLE a ha _) (𝟙 _)
    refine ⟨h1, fun G i _ hG ↦ ?_⟩
    have : K.obj.IsGE (-1) := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (h1 i hi)
    have hM : (singleComplex (-1) G).IsCurvePerverseLE (-1) :=
      ⟨fun b hb ↦ isZero_homologySheaf_singleComplex (by omega) G, by
        rw [WeilSheaf.support_congr (homologySheafSingleComplexIso (-1) G)]
        exact hG⟩
    obtain rfl := key (-1) G hM i
    exact IsZero.of_mono_zero G ((homologySheaf (-1)).obj K)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Basic objects of the curve perverse heart**: a Weil sheaf of finite support, placed in
degree zero, is curve perverse; these are the objects `i_{x*}E` of the blueprint and their
finite sums. (blueprint: `thm-a1-curve-perverse-heart`) -/
theorem isCurvePerverse_toComplex_obj (G : WeilSheaf k₀ l X) (hG : G.support.Finite) :
    (WeilSheaf.toComplex.obj G).IsCurvePerverse := by
  have hz (a : ℤ) (ha : a ≠ 0) : IsZero ((homologySheaf a).obj (WeilSheaf.toComplex.obj G)) := by
    refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_
    change IsZero ((_root_.DerivedCategory.homologyFunctor _ a).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))
    obtain ha | ha := ha.lt_or_gt
    · exact (_root_.DerivedCategory.isGE_iff _ 0).1 inferInstance a ha
    · exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance a ha
  refine ⟨⟨fun a ha ↦ hz a ha.ne', ?_⟩,
    ⟨fun a ha ↦ hz a (by omega), fun G' i _ _ ↦ IsZero.of_mono i (hz (-1) (by norm_num))⟩⟩
  have e : (homologySheaf 0).obj (WeilSheaf.toComplex.obj G) ≅ G :=
    WeilSheaf.toComplexCompHomologySheafIso.app G
  rw [WeilSheaf.support_congr e]
  exact hG

end Curve

end WeilComplex

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The affine line has two distinct points: the generic point and a closed point, the
polynomial ring `k₀[x]` not being a field. -/
instance _root_.AlgebraicGeometry.affineLine.nontrivial (k₀ : Type u) [Field k₀] :
    Nontrivial (affineLine k₀) := by
  let e := AffineSpace.SpecIso PUnit.{u + 1} (CommRingCat.of k₀)
  let R := MvPolynomial PUnit.{u + 1} (CommRingCat.of k₀)
  have hR : ¬ IsField R := fun h ↦ Polynomial.not_isField (R := k₀)
    (MulEquiv.isField h (MvPolynomial.uniqueAlgEquiv k₀ PUnit.{u + 1}).symm.toMulEquiv)
  obtain ⟨I, hI1, hI2⟩ := (Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top).1 hR
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI2.ne
  let p : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum R := ⟨M, hM.isPrime⟩
  have hpq : p ≠ q := fun h ↦
    hI1.ne' (le_bot_iff.1 (hIM.trans (congrArg PrimeSpectrum.asIdeal h).symm.le))
  exact ⟨⟨e.inv.base p, e.inv.base q, fun h ↦ hpq (e.inv.isOpenEmbedding.injective h)⟩⟩

open scoped ProEtale in
/-- **A middle extension has no punctual subsheaf**: every morphism from a Weil sheaf `G` of
finite support on the affine line to the direct image `j_*M` of a lisse Weil sheaf on a dense
open vanishes. Let `V₀` be the complement of the support of `G`; then `G|_{V₀} = 0`, its stalks
at the closed points of `V₀` vanishing. The adjoint `j̄^* G ⟶ M` of the morphism therefore
vanishes on `Ū ∩ V̄₀`, and every point of `Ū` specializes from a point of `Ū ∩ V̄₀`, namely from
the generic point of the irreducible geometric line, which lies over `V₀` since the affine line
is not a single closed point. A morphism into the lisse `M` vanishing there vanishes
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero`).
(blueprint: `thm-a1-curve-perverse-heart`, Step 0) -/
theorem LisseOnDenseOpen.eq_zero_of_support_finite (D : LisseOnDenseOpen k₀ l)
    {G : WeilSheaf k₀ l (affineLine k₀)} (hG : G.support.Finite) (i : G ⟶ D.directImage) :
    i = 0 := by
  classical
  set S : Set (affineLine k₀) := ⋃ x ∈ G.support, {x.1} with hS
  have hSc : IsClosed S :=
    hG.isClosed_biUnion fun x _ ↦ (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
  let V₀ : (affineLine k₀).Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  -- `G` vanishes on `V₀`
  have hz : IsZero ((upperStar V₀.ι).obj G) := by
    refine isZero_upperStar_of_forall_notMem_support V₀.ι G fun y hy ↦ ?_
    have hV : V₀.ι.base y.1 ∈ (V₀ : Set (affineLine k₀)) := by
      rw [Scheme.Opens.ι_apply]
      exact y.1.2
    exact hV (Set.mem_biUnion hy rfl)
  set jb := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  set gb := Scheme.Hom.geometricFiberMap V₀.ι (comp_over V₀.ι (Spec (CommRingCat.of k₀)))
  set prA := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  have : IrreducibleSpace (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    Scheme.Hom.irreducibleSpace_geometricFiber _
  -- the generic point of the geometric line lies over `V₀`
  have hξ : prA.base (genericPoint _) ∈ (V₀ : Set (affineLine k₀)) := by
    intro hS
    obtain ⟨x, -, hxe⟩ := Set.mem_iUnion₂.1 hS
    have hcl := (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
    rw [Set.mem_singleton_iff] at hxe
    obtain ⟨a, b, hab⟩ := affineLine.nontrivial k₀
    have key (z : affineLine k₀) : z = x.1 := by
      obtain ⟨z', hz'⟩ :=
        Scheme.Hom.geometricFiberProj_surjective (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) z
      have h1 := ((genericPoint_spec _).specializes (Set.mem_univ z')).map prA.continuous
      rw [hz', hxe] at h1
      exact h1.mem_closed hcl rfl
    exact hab ((key a).trans (key b).symm)
  -- every point of `Ū` specializes from a point of `Ū ∩ V̄₀`
  have hgen : ∀ y, ∃ p : (Limits.pullback jb gb : Scheme.{u}),
      (pullback.fst jb gb).base p ⤳ y := by
    intro y
    have h1 := (genericPoint_spec
      ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)).specializes
        (Set.mem_univ (jb.base y))
    obtain ⟨η, hη⟩ : genericPoint _ ∈ Set.range jb.base :=
      h1.mem_open jb.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
    obtain ⟨v, hv1, -⟩ := Scheme.exists_preimage_of_isPullback
      (Scheme.Hom.isPullback_geometricFiberMap V₀.ι (comp_over V₀.ι _))
      (genericPoint _) ⟨_, hξ⟩ (by rw [Scheme.Opens.ι_apply])
    obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := jb) (g := gb) η v
      (hη.trans hv1.symm)
    refine ⟨p, ?_⟩
    rw [hp1]
    rw [← hη] at h1
    exact jb.isOpenEmbedding.isInducing.specializes_iff.1 h1
  -- the adjoint morphism `j̄^* G ⟶ M` vanishes
  have hcar : IsZero ((gb)^*ᵃ[l].obj G.obj.carrier) := isZero_iff_isZero_carrier.1 hz
  let adj := ProEtale.adicUpperStarLowerStarAdjunction l jb
  let φ := (adj.homEquiv _ _).symm i.hom.hom.f
  have hφ : (pullback.fst jb gb)^*ᵃ[l].map φ = 0 :=
    ((Functor.map_isZero ((pullback.snd jb gb)^*ᵃ[l]) hcar).of_iso
      ((ProEtale.adicUpperStarCompIso l (pullback.condition (f := jb) (g := gb))).app
        G.obj.carrier)).eq_of_src _ _
  have hφ0 : φ = 0 :=
    ProEtale.IsAdicLisseSheaf.eq_zero_of_adicUpperStar_map_eq_zero _ hgen D.lisse φ hφ
  have hf : i.hom.hom.f = 0 := by
    rw [← (adj.homEquiv _ _).apply_symm_apply i.hom.hom.f]
    change adj.homEquiv _ _ φ = 0
    rw [hφ0, Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]
  exact ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Endofunctor.Algebra.Hom.ext hf

/-- **Basic objects of the curve perverse heart**: the middle extension `(j_*M)[1]` of a lisse
Weil sheaf on a dense open of the affine line is curve perverse. Its only cohomology sheaf is
`𝓗⁻¹ = j_*M`, which has no nonzero punctual subsheaf
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_zero_of_support_finite`).
(blueprint: `thm-a1-curve-perverse-heart`) -/
theorem LisseOnDenseOpen.isCurvePerverse_middleExtension (D : LisseOnDenseOpen k₀ l) :
    D.middleExtension.IsCurvePerverse := by
  have hz (a : ℤ) (ha : a ≠ -1) :
      IsZero ((WeilComplex.homologySheaf a).obj D.middleExtension) :=
    WeilComplex.isZero_homologySheaf_shift_toComplex _ (by omega)
  let e : (WeilComplex.homologySheaf (-1 : ℤ)).obj D.middleExtension ≅ D.directImage :=
    WeilComplex.homologySheafShiftToComplexIso _ 1 (-1) (by norm_num)
  refine ⟨⟨fun a ha ↦ hz a (by omega), ?_⟩, ⟨fun a ha ↦ hz a (by omega), fun G i _ hG ↦ ?_⟩⟩
  · rw [WeilSheaf.support_eq_empty_of_isZero (hz 0 (by norm_num))]
    exact Set.finite_empty
  · have h1 : i = 0 :=
      (cancel_mono e.hom).1 ((D.eq_zero_of_support_finite hG _).trans zero_comp.symm)
    subst h1
    exact IsZero.of_mono_zero G ((WeilComplex.homologySheaf (-1 : ℤ)).obj D.middleExtension)

end WeilSheaf

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The curve perverse Weil complexes on the affine line, as a full subcategory: the heart
`Perv(A₀)` of the perverse t-structure. -/
abbrev curvePerverse : ObjectProperty (WeilComplex k₀ l (affineLine k₀)) :=
  IsCurvePerverse

/-- **Simple perverse sheaves on the affine line**: a curve perverse Weil complex is simple in
`Perv(A₀)` exactly when it is either a simple Weil sheaf of finite support placed in degree
zero — a punctual object `i_{x*}E` with `E` irreducible — or the middle extension `(j_*N)[1]`
of an irreducible lisse sheaf `N` on a dense open. (blueprint: `prop-a1-curve-perverse-simples`)
-/
theorem simple_iff (P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory) :
    Simple P ↔
      (∃ G : WeilSheaf k₀ l (affineLine k₀), Simple G ∧ G.support.Finite ∧
        Nonempty (P.obj ≅ WeilSheaf.toComplex.obj G)) ∨
      ∃ D : WeilSheaf.LisseOnDenseOpen k₀ l, D.sheaf.IsIrreducibleLisse ∧
        Nonempty (P.obj ≅ D.middleExtension) :=
  -- TODO(adic): the exact sequences of the heart and the surjectivity of `π₁(U') → π₁(U)`
  sorry

end WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The middle extension `(j_*M)[1]` of an irreducible lisse sheaf is a simple object of the
curve perverse heart. (blueprint: `prop-a1-curve-perverse-simples`) -/
theorem WeilSheaf.LisseOnDenseOpen.simple_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) :
    Simple (⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩ :
      WeilComplex.curvePerverse.FullSubcategory) :=
  (WeilComplex.simple_iff _).2 (.inr ⟨D, hD, ⟨Iso.refl _⟩⟩)

/-- **The Fourier transform is perverse t-exact on the line**, upper classes: for a nontrivial
`ψ`, the transform `FT_ψ` carries `ᵖD^{≤n}(A₀)` into `ᵖD^{≤n}(A'₀)`. Its stalks are computed by
the stalk formula, its degree-zero cohomology sheaf has finite support because at most
`rank 𝓖` pairwise distinct characters `ℒ_{ψ(-ax)}` are quotients of the generic
representation of `𝓖`, and a sheaf of finite support transforms into a lisse sheaf shifted by
one. (blueprint: `thm-a1-fourier-t-exact`) -/
theorem isCurvePerverseLE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {n : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.IsCurvePerverseLE n) :
    ((fourierTransform ψ).obj K).IsCurvePerverseLE n :=
  -- TODO(adic): the stalk formula, the coinvariant description of `H_c²` and the linear
  -- independence of distinct characters
  sorry

/-- **The Fourier transform is perverse t-exact on the line**, upper classes for the inverse:
the inverse of the equivalence `FT_ψ`, which is `FT_{ψ⁻¹}(-)(1)` by Fourier inversion, carries
`ᵖD^{≤n}(A'₀)` into `ᵖD^{≤n}(A₀)`, by the argument for `FT_{ψ⁻¹}` and the twist being the
tensor product with a lisse sheaf of rank one. (blueprint: `thm-a1-fourier-t-exact`) -/
theorem isCurvePerverseLE_fourierTransform_inv_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {n : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.IsCurvePerverseLE n) :
    haveI := isEquivalence_fourierTransform (l := l) ψ hψ
    ((fourierTransform ψ).inv.obj K).IsCurvePerverseLE n :=
  -- TODO(adic): Fourier inversion `FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)` and the argument for `FT_{ψ⁻¹}`
  sorry

/--
The Fourier–Deligne transform along a nontrivial additive character is exact for the curve
perverse t-structures of the two dual affine lines: a Weil complex is curve perverse exactly
when its transform is.

```
  Dᵇ(A₀) ──────FT_ψ──────▶ Dᵇ(A'₀)
     ∪                        ∪
  Perv(A₀) ────≃ exact───▶ Perv(A'₀)
```
(blueprint: `sk-p-dl-a1-perverse`)
-/
theorem isCurvePerverse_fourierTransform_obj_iff (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).IsCurvePerverse ↔ K.IsCurvePerverse := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨(isCurvePerverseLE_fourierTransform_inv_obj ψ hψ hU).of_iso
      ((fourierTransform ψ).asEquivalence.unitIso.app K).symm, ?_⟩
    rw [WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero] at hL ⊢
    intro M hM f
    apply (fourierTransform ψ).map_injective
    rw [hL _ (isCurvePerverseLE_fourierTransform_obj ψ hψ hM) ((fourierTransform ψ).map f),
      Functor.map_zero]
  · rintro ⟨hU, hL⟩
    refine ⟨isCurvePerverseLE_fourierTransform_obj ψ hψ hU, ?_⟩
    rw [WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero] at hL ⊢
    intro M hM f
    let e := (fourierTransform ψ).asEquivalence.counitIso.app M
    obtain ⟨g, hg⟩ := (fourierTransform ψ).map_surjective (e.hom ≫ f)
    rw [← cancel_epi e.hom, comp_zero]
    exact hg.symm.trans ((congrArg (fourierTransform ψ).map
      (hL _ (isCurvePerverseLE_fourierTransform_inv_obj ψ hψ hM) g)).trans (Functor.map_zero _ _ _))

/-- `FT_ψ` preserves simple objects of the curve perverse heart: by Fourier inversion
(`AlgebraicGeometry.isEquivalence_fourierTransform`) and perversity
(`AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`) it restricts to an
autoequivalence of the heart, and equivalences preserve simple objects.
(blueprint: `prop-a1-fourier-middle-extension`, Step 1) -/
theorem simple_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : (WeilComplex.curvePerverse (k₀ := k₀) (l := l)).FullSubcategory) [Simple K] :
    Simple (⟨(fourierTransform ψ).obj K.obj,
      (isCurvePerverse_fourierTransform_obj_iff ψ hψ K.obj).2 K.property⟩ :
        WeilComplex.curvePerverse.FullSubcategory) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  have hP : WeilComplex.curvePerverse.inverseImage (fourierTransform ψ).asEquivalence.functor =
      WeilComplex.curvePerverse :=
    funext fun K ↦ propext (isCurvePerverse_fourierTransform_obj_iff ψ hψ K)
  exact simple_obj ((fourierTransform ψ).asEquivalence.congrFullSubcategory hP).functor K

end AlgebraicGeometry
