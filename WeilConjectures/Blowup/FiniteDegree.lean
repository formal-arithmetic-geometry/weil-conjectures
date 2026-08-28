/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Affine.Principalization
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Proper
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-!

# Finite-degree approximation on the blow-up (Stacks Project Tag 0803)

This file proves the finite-degree approximation of a finite-type center on a blow-up:
for finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there
are `d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is
`I_E^d · J` (`Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`, Stacks
Project Tag 0803; blueprint: `blueprint/finite_degree_approximation_blowup.tex`,
`lemma:nagata-proj-closed-center-finite-degree-exists`).

The proof is organized around the maximal degree-`d` candidate
`I^d ⊓ π₎(I_E^d·J)`: over an affine open `V` of the base, the blow-up is covered by
the charts at the degree-one Rees elements of a finite generating set of `I(V)`, and
each finite chart-ideal generator `μ = g/aᵉ` of `J` is cleared into a numerator
`m = aᴺ·g ∈ I(V)^d` with `m/aᵈ = μ` whose fractions `m/bᵈ` lie in the chart ideals of
every chart of the same Rees algebra (`AffineBlowup.exists_uniform_numerator`, the
denominator-clearing core). A finite-type subsheaf through the finitely many
numerators is then extracted with the Tag 01PF machinery
(`Scheme.IdealSheafData.exists_finiteType_le_ideal_eq`), and generates `I_E^d · J`
chart by chart (`Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators`).

Elaboration-performance conventions: the chart rings of the blow-up are large
`HomogeneousLocalization` types, so all `Finset` bookkeeping over generating sets is
done by the abstract combinators `exists_uniform_ge₂`/`exists_finset_forall_mem` over
variable types, chart probes keep their ring abstract
(`Scheme.IdealSheafData.ideal_comap_comap_of_probe`), and memberships are transported
along morphism equalities by `mem_of_ringHom_eq` instead of `▸`-rewrites.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Pullback of ideal sheaves along an open immersion commutes with products. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_mul_of_isOpenImmersion
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (I K : Z.IdealSheafData) :
    (I * K).comap f = I.comap f * K.comap f := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, CommRingCat.comap_inv_eq_map,
    Ideal.map_mul]

/-- Pullback of ideal sheaves along an open immersion commutes with powers. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_pow_of_isOpenImmersion
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] (I : Z.IdealSheafData) (d : ℕ) :
    (I ^ d).comap f = (I.comap f) ^ d := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, CommRingCat.comap_inv_eq_map,
    Ideal.map_pow]

/-- The pullback of a finite-type ideal sheaf along an open immersion is finite type. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType.comap_of_isOpenImmersion
    {Y Z : Scheme.{u}} {K : Z.IdealSheafData} (hK : K.ofFiniteType) (f : Y ⟶ Z)
    [IsOpenImmersion f] : (K.comap f).ofFiniteType := fun U' _ ↦
  (Scheme.IdealSheafData.fg_ideal_comap_iff f K U').mpr (hK _ le_top)

/-- Finite-type ideal sheaves are stable under products. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ofFiniteType.mul
    {X : Scheme.{u}} {I K : X.IdealSheafData}
    (hI : I.ofFiniteType) (hK : K.ofFiniteType) : (I * K).ofFiniteType := by
  intro U _
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact (hI U le_top).mul (hK U le_top)

/-- The ideal of sections on `⊤` of `ofIdealTop`. -/
private lemma ideal_top_ofIdealTop {Y : Scheme.{u}} [IsAffine Y] (K : Ideal Γ(Y, ⊤)) :
    (Scheme.IdealSheafData.ofIdealTop K).ideal ⟨⊤, isAffineOpen_top _⟩ = K := by
  have h1 : Y.presheaf.map ((homOfLE le_top).op :
      Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (((⟨⊤, isAffineOpen_top Y⟩ :
        Y.affineOpens) : Y.Opens))) = 𝟙 _ := Y.presheaf.map_id _
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, h1, CommRingCat.hom_id, Ideal.map_id]

/-- **Finite-type subsheaves through prescribed sections** (a corollary of the
finite-type extension theorem, Stacks Project Tag 01PF): if `F` is a finitely generated
subideal of the sections of an ideal sheaf `H` over an affine open `V` of a qcqs
scheme, there is a finite-type ideal sheaf `L ≤ H` whose ideal of sections over `V` is
exactly `F`. The extension theorem is applied to the ambient
`(K_F.map V.ι) ⊓ H`, where `K_F` is the ideal sheaf on `V` generated by `F`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_le_ideal_eq
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (H : X.IdealSheafData)
    (V : X.affineOpens) {F : Ideal Γ(X, V.1)} (hF : F.FG) (hFH : F ≤ H.ideal V) :
    ∃ L : X.IdealSheafData, L ≤ H ∧ L.ofFiniteType ∧ L.ideal V = F := by
  haveI : IsAffine V.1.toScheme := V.2
  haveI : CompactSpace V.1.toScheme := isCompact_iff_compactSpace.mp V.2.isCompact
  have htop : (⊤ : V.1.toScheme.Opens) ≤ V.1.ι ⁻¹ᵁ V.1 := V.1.ι_preimage_self.ge
  -- the ideal sheaf on `V` generated by `F`
  set K : V.1.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (F.map (V.1.ι.appLE V.1 ⊤ htop).hom) with hKdef
  have hKtop : K.ideal ⟨⊤, isAffineOpen_top _⟩ = F.map (V.1.ι.appLE V.1 ⊤ htop).hom :=
    ideal_top_ofIdealTop _
  have hKle : K ≤ H.comap V.1.ι := by
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    rw [hKtop, Scheme.IdealSheafData.ideal_comap_eq_map_appLE V.1.ι H V
      ⟨⊤, isAffineOpen_top _⟩ htop]
    exact Ideal.map_mono hFH
  have hH'comap : ((K.map V.1.ι) ⊓ H).comap V.1.ι = K := by
    rw [Scheme.IdealSheafData.comap_inf_of_isOpenImmersion,
      Scheme.IdealSheafData.comap_map, inf_eq_left.mpr hKle]
  obtain ⟨L, hle, hft, hcomap⟩ := Scheme.IdealSheafData.exists_finiteType_le_comap_eq
    ((K.map V.1.ι) ⊓ H) V.1 V.2.isCompact (by
      rw [Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap, hH'comap]
      intro U' _
      rw [hKdef, Scheme.IdealSheafData.ofIdealTop_ideal]
      exact (hF.map _).map _)
  rw [hH'comap] at hcomap
  refine ⟨L, hle.trans inf_le_right, hft, ?_⟩
  -- evaluate the comap identity at `⊤` and cancel the section isomorphism
  have h1 : (L.ideal V).map (V.1.ι.appLE V.1 ⊤ htop).hom =
      F.map (V.1.ι.appLE V.1 ⊤ htop).hom := by
    have h2 := congrArg (fun T : V.1.toScheme.IdealSheafData ↦
      T.ideal ⟨⊤, isAffineOpen_top _⟩) hcomap
    dsimp only at h2
    rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE V.1.ι L V ⟨⊤, isAffineOpen_top _⟩
      htop, hKtop] at h2
    exact h2
  haveI : IsIso (V.1.ι.appLE V.1 ⊤ htop) := inferInstance
  have hbij : Function.Bijective (V.1.ι.appLE V.1 ⊤ htop).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h3 := congrArg (Ideal.comap (V.1.ι.appLE V.1 ⊤ htop).hom) h1
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h3

section FiniteDegreeAlgebra

/-! ### Chart algebra for the finite-degree approximation (Stacks Tag 0803)

The finite-degree approximation `exists_finiteDegree_center_le_blowup` below requires,
over a single affine open with Rees algebra `⊕ Iⁿ`, the algebra of degree-`e` chart
fractions `g/aᵉ` on the `a`-chart of the blow-up, together with the comparison of two
charts through the localization `B_a → B_{a·b}` of `HomogeneousLocalization.awayMap`
(whose localizing element is exactly the chart fraction `b/a`, by
`HomogeneousLocalization.Away.isLocalization_mul`). -/

open HomogeneousLocalization Polynomial

/-- **Clearing denominators in a localization**: if the image of `x` under the
localization map away from `t` lies in the extension of an ideal `K`, then some power
of `t` multiplies `x` into `K`. -/
lemma _root_.Ideal.exists_pow_mul_mem_of_algebraMap_mem_map {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (t : R) [IsLocalization.Away t S] {K : Ideal R} {x : R}
    (hx : algebraMap R S x ∈ K.map (algebraMap R S)) :
    ∃ k : ℕ, t ^ k * x ∈ K := by
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) S).mp hx
  obtain ⟨k₁, hk₁⟩ := u.2
  have hu : (u : R) = t ^ k₁ := hk₁.symm
  have h0 : algebraMap R S (x * t ^ k₁ - j) = 0 := by
    rw [map_sub, map_mul, sub_eq_zero, ← hu]
    exact hju
  obtain ⟨⟨-, k₂, rfl⟩, hk₂⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers t) S _).mp h0
  refine ⟨k₂ + k₁, ?_⟩
  have h1 : t ^ (k₂ + k₁) * x = t ^ k₂ * (j : R) := by
    have h2 : t ^ k₂ * (x * t ^ k₁ - (j : R)) = 0 := hk₂
    rw [pow_add]
    linear_combination h2
  rw [h1]
  exact K.mul_mem_left _ j.2

/-- Membership in the image of an ideal under an isomorphism of commutative rings. -/
lemma _root_.CommRingCat.hom_mem_ideal_map_iso_iff {R S : CommRingCat.{u}} (e : R ≅ S)
    (P : Ideal R) (x : R) : e.hom.hom x ∈ P.map e.hom.hom ↔ x ∈ P := by
  conv_rhs =>
    rw [← Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso e.hom)
      (I := P)]
  exact Iff.rfl

/-- The degree-one Rees elements are additive in the section. -/
lemma _root_.AlgebraicGeometry.reesX_add {A : Type u} [CommRing A] (I : Ideal A)
    {b₁ b₂ : A} (hb₁ : b₁ ∈ I)
    (hb₂ : b₂ ∈ I) :
    reesX I (b₁ + b₂) (add_mem hb₁ hb₂) = reesX I b₁ hb₁ + reesX I b₂ hb₂ := by
  apply Subtype.ext
  push_cast [coe_reesX]
  exact map_add (Polynomial.monomial 1) b₁ b₂

/-- **The chart basic opens at a generating set cover the affine blow-up**: for a
finite generating set `s` of `I`, the basic opens at the degree-one elements `a·X`,
`a ∈ s`, already cover `Proj` of the Rees algebra. This is the covering core of
`AffineBlowup.compactSpace_of_fg` below. -/
lemma _root_.AlgebraicGeometry.AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span
    {A : Type u} [CommRing A]
    {I : Ideal A} {s : Finset A} (hs : Ideal.span (s : Set A) = I) :
    ⨆ a : s, Proj.basicOpen (reesGrading I)
      (reesX I a.1 (hs ▸ Ideal.subset_span a.2)) = ⊤ := by
  classical
  have hmem : ∀ a ∈ s, (a : A) ∈ I := fun a ha ↦ hs ▸ Ideal.subset_span ha
  refine Proj.iSup_basicOpen_eq_top (reesGrading I) _ ?_
  refine (irrelevant_le_span_range_reesX I).trans (Ideal.span_le.mpr ?_)
  rintro - ⟨b, rfl⟩
  have key : ∀ (c : A) (_ : c ∈ Ideal.span (s : Set A)), ∀ hcI : c ∈ I,
      reesX I c hcI ∈ Ideal.span (Set.range fun a : s ↦
        reesX I a.1 (hs ▸ Ideal.subset_span a.2)) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx => exact fun hcI ↦ Ideal.subset_span ⟨⟨x, hx⟩, rfl⟩
    | zero =>
      intro h0
      have hz : reesX I 0 h0 = 0 := by
        apply Subtype.ext
        push_cast [coe_reesX]
        simp
      rw [hz]
      exact zero_mem _
    | add x y hx hy ihx ihy =>
      intro hxy
      have hxI : x ∈ I := hs ▸ hx
      have hyI : y ∈ I := hs ▸ hy
      rw [show reesX I (x + y) hxy = reesX I x hxI + reesX I y hyI from
        reesX_add I hxI hyI]
      exact add_mem (ihx hxI) (ihy hyI)
    | smul a x hx ih =>
      intro hax
      have hxI : x ∈ I := hs ▸ hx
      have hmul : reesX I (a • x) hax =
          reesMonomial I (n := 0) a (by rw [pow_zero, Ideal.one_eq_top]; trivial) *
            reesX I x hxI := by
        apply Subtype.ext
        push_cast [coe_reesX]
        simp [smul_eq_mul]
      rw [hmul]
      exact Ideal.mul_mem_left _ _ (ih hxI)
  exact key b.1 (hs.symm ▸ b.2) b.2

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- The degree-`n` chart fraction `g/aⁿ` on the `a`-chart of the affine blow-up, for
`g ∈ I₀ⁿ`: the homogeneous fraction `(g·Xⁿ)/((a·X)ⁿ)`. -/
noncomputable def _root_.AlgebraicGeometry.AffineBlowup.chartFrac
    {a : A} (ha : a ∈ I₀) {n : ℕ} {g : A}
    (hg : g ∈ I₀ ^ n) :
    HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha) :=
  HomogeneousLocalization.Away.mk (reesGrading I₀) (reesX_mem I₀ a ha) n
    (reesMonomial I₀ g hg) (by simpa using reesMonomial_mem I₀ g hg)

/-- Multiplying the chart fraction `g/aⁿ` by `aⁿ` recovers `g`: division by powers of
`a` is possible on the `a`-chart for every section of the corresponding power of the
center. -/
lemma _root_.AlgebraicGeometry.AffineBlowup.chartFrac_mul_awayAlgebraMap_pow
    {a : A} (ha : a ∈ I₀) {n : ℕ}
    {g : A} (hg : g ∈ I₀ ^ n) :
    AffineBlowup.chartFrac I₀ ha hg *
        AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a ha) a ^ n =
      AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a ha) g := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_pow, AffineBlowup.val_awayAlgebraMap,
    AffineBlowup.val_awayAlgebraMap, AffineBlowup.chartFrac,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesGradingZero_apply, coe_reesX]
  rw [Polynomial.monomial_pow, one_pow, ← Polynomial.C_pow]
  simp only [Polynomial.monomial_mul_C, one_mul, mul_one]
  rw [mul_comm g]

/-- The localizing element `(b·X)/(a·X)` of the chart comparison, multiplied by `a`,
gives `b` on the `a`-chart. -/
lemma _root_.AlgebraicGeometry.AffineBlowup.isLocalizationElem_mul_awayAlgebraMap
    {a b : A} (ha : a ∈ I₀)
    (hb : b ∈ I₀) :
    HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ a ha)
        (reesX_mem I₀ b hb) *
        AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a ha) a =
      AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a ha) b := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    AffineBlowup.val_awayAlgebraMap, AffineBlowup.val_awayAlgebraMap,
    HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesX, coe_reesGradingZero_apply]
  simp only [pow_one, one_mul, mul_one, Polynomial.monomial_mul_C]
  rw [mul_comm b]

/-- **The chart-overlap identity**: in the common localization `B_{a·b}` of the `a`- and
`b`-charts, the degree-`n` chart fraction `g/aⁿ` of the `a`-chart equals the chart
fraction `g/bⁿ` of the `b`-chart multiplied by the `n`-th power of the localizing
element `(b·X)/(a·X)`. -/
lemma _root_.AlgebraicGeometry.AffineBlowup.awayMap_chartFrac
    {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀) {n : ℕ}
    {g : A} (hg : g ∈ I₀ ^ n) :
    HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (rfl : reesX I₀ a ha * reesX I₀ b hb = reesX I₀ a ha * reesX I₀ b hb)
        (AffineBlowup.chartFrac I₀ ha hg) =
      HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
          (mul_comm (reesX I₀ a ha) (reesX I₀ b hb))
          (AffineBlowup.chartFrac I₀ hb hg) *
        HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
          (rfl : reesX I₀ a ha * reesX I₀ b hb = reesX I₀ a ha * reesX I₀ b hb)
          (HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ a ha)
            (reesX_mem I₀ b hb)) ^ n := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac,
    HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  ring

end FiniteDegreeAlgebra

section FiniteDegreeBlowup

/-! ### Chart probes of the blow-up and their pulled-back ideals

For the finite-degree approximation we probe the blow-up `Bl_I X` by the affine charts
over an affine open `V` of the base at the degree-one Rees elements `a·X`, `a ∈ I(V)`.
We compute the ideal of global sections of the pullback of an ideal sheaf along such a
probe, and along a probe precomposed with `Spec` of a ring map. -/

open HomogeneousLocalization

/-- Comparing two ideals through the pullback along a bijective ring homomorphism. -/
lemma _root_.Ideal.le_of_comap_le_comap_of_bijective {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (hf : Function.Bijective f) {P Q : Ideal S}
    (h : P.comap f ≤ Q.comap f) : P ≤ Q := by
  intro x hx
  obtain ⟨y, rfl⟩ := hf.2 x
  exact h (Ideal.mem_comap.mpr hx)

variable {X : Scheme.{u}}

/-- The chart probe of the blow-up over an affine open `V` at a section `a ∈ I(V)`: the
affine chart of the affine blow-up at the degree-one Rees element `a·X`, embedded into
the blow-up. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))) ⟶ I.blowup :=
  AffineBlowup.chart (I.ideal V) (reesX (I.ideal V) a ha)
    (reesX_mem (I.ideal V) a ha) ≫ I.blowupι V

instance (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    IsOpenImmersion (I.blowupChart V ha) := by
  unfold Scheme.IdealSheafData.blowupChart
  infer_instance

/-- The map on section rings induced by the chart probe of the blow-up. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChartSection
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Γ(X, V.1) ⟶ Γ(Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))), ⊤) :=
  CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
    (reesX (I.ideal V) a ha)) ≫ (Scheme.ΓSpecIso _).inv

/-- The chart probe composed with the blow-up map is the affine probe of the chart
ring. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart_comp_blowupMap
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    I.blowupChart V ha ≫ I.blowupMap =
      Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
        (reesX (I.ideal V) a ha))) ≫ V.2.fromSpec := by
  unfold Scheme.IdealSheafData.blowupChart
  rw [Category.assoc, Scheme.IdealSheafData.blowupι_blowupMap,
    Scheme.IdealSheafData.blowupNatTrans_app, Category.assoc,
    AffineBlowup.chart_toSpec_assoc, IsAffineOpen.isoSpec_inv_ι]

/-- The chart probe lies over the affine open `V`. Derived from the abstract-probe
form `top_le_preimage_specMap_fromSpec`, which keeps the chart ring out of the
rewrite motives. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.blowupChart_comp_blowupMap_preimage
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    (⊤ : (Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) a ha)))).Opens) ≤
      (I.blowupChart V ha ≫ I.blowupMap) ⁻¹ᵁ V.1 :=
  le_of_le_of_eq (top_le_preimage_specMap_fromSpec V _)
    (congrArg (fun f : Spec _ ⟶ X ↦ f ⁻¹ᵁ V.1)
      (I.blowupChart_comp_blowupMap V ha)).symm

/-- Rewriting `appLE` along an equality of morphisms. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.appLE_eq_of_eq {T T' : Scheme.{u}}
    {f g : T ⟶ T'} (hfg : f = g) (U : T'.Opens) (V' : T.Opens) (e : V' ≤ f ⁻¹ᵁ U) :
    f.appLE U V' e = g.appLE U V' (hfg ▸ e) := by
  subst hfg
  rfl

/-- The `appLE` of the chart probe over `V` is the chart section map. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.appLE_blowupChart_comp_blowupMap
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V)
    (h : (⊤ : (Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) a ha)))).Opens) ≤ (I.blowupChart V ha ≫ I.blowupMap) ⁻¹ᵁ V.1) :
    (I.blowupChart V ha ≫ I.blowupMap).appLE V.1 ⊤ h = I.blowupChartSection V ha := by
  rw [Scheme.Hom.appLE_eq_of_eq (I.blowupChart_comp_blowupMap V ha)]
  exact appLE_top_specMap_fromSpec V (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap
    (I.ideal V) (reesX (I.ideal V) a ha))) _

/-- **Pullback of an ideal sheaf along a precomposed affine probe**: precomposing a
probe `Spec S ⟶ Y` with `Spec` of a ring map `β` extends the pulled-back ideal of
global sections along the induced map of section rings. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_specMap_comp
    {Y : Scheme.{u}} (K : Y.IdealSheafData) {S S' : CommRingCat.{u}} (q : Spec S ⟶ Y)
    (β : S ⟶ S') :
    (K.comap (Spec.map β ≫ q)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((K.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
        ((Scheme.ΓSpecIso S).hom ≫ β ≫ (Scheme.ΓSpecIso S').inv).hom := by
  have hfac : Spec.map β =
      Spec.map ((Scheme.ΓSpecIso S).hom ≫ β) ≫ (isAffineOpen_top (Spec S)).fromSpec := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rw [show (Scheme.ΓSpecIso S).inv ≫ (Scheme.ΓSpecIso S).hom ≫ β = β from
      Iso.inv_hom_id_assoc _ _]
  rw [Scheme.IdealSheafData.comap_comp, hfac,
    Scheme.IdealSheafData.ideal_top_comap_specMap_fromSpec (K.comap q)
      ⟨⊤, isAffineOpen_top _⟩ ((Scheme.ΓSpecIso S).hom ≫ β),
    Ideal.map_map, ← CommRingCat.hom_comp, Category.assoc]

/-- The variant of `ideal_comap_specMap_comp` after transport to the affine section
rings: precomposition extends the pulled-back ideal along `β` itself. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_comap_specMap_comp
    {Y : Scheme.{u}} (K : Y.IdealSheafData) {S S' : CommRingCat.{u}} (q : Spec S ⟶ Y)
    (β : S ⟶ S') :
    ((K.comap (Spec.map β ≫ q)).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (Scheme.ΓSpecIso S').hom.hom =
      (((K.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
        (Scheme.ΓSpecIso S).hom.hom).map β.hom := by
  rw [K.ideal_comap_specMap_comp q β, Ideal.map_map, Ideal.map_map,
    ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 2
  simp

/-- **Pullback of an inverse image ideal sheaf along a probe of the blow-up** lying
over an affine probe of the base. The probe ring `S` is kept abstract: this makes the
lemma cheap to instantiate at the large `HomogeneousLocalization` chart rings of the
blow-up, where every unification involving the concrete ring is prohibitively slow. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_of_probe
    (I K : X.IdealSheafData) {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup)
    (V : X.affineOpens) (φ : Γ(X, V.1) ⟶ S)
    (hc : c ≫ I.blowupMap = Spec.map φ ≫ V.2.fromSpec) :
    ((K.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.ideal V).map (φ ≫ (Scheme.ΓSpecIso S).inv).hom := by
  rw [← Scheme.IdealSheafData.comap_comp, hc,
    K.ideal_top_comap_specMap_fromSpec V φ, CommRingCat.hom_comp, ← Ideal.map_map]

/-- The principal case of `ideal_comap_comap_of_probe`: if the extension of `K(V)`
along `φ` is generated by the image of a section `b`, so is the pullback of the
inverse image of `K` along the probe. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_of_probe_span
    (I K : X.IdealSheafData) {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup)
    (V : X.affineOpens) (φ : Γ(X, V.1) ⟶ S)
    (hc : c ≫ I.blowupMap = Spec.map φ ≫ V.2.fromSpec) {b : Γ(X, V.1)}
    (hspan : (K.ideal V).map φ.hom = Ideal.span {φ.hom b}) :
    ((K.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(φ ≫ (Scheme.ΓSpecIso S).inv).hom b} := by
  rw [Scheme.IdealSheafData.ideal_comap_comap_of_probe I K c V φ hc,
    CommRingCat.hom_comp, RingHom.comp_apply, ← Ideal.map_map, hspan, Ideal.map_span,
    Set.image_singleton]

/-- Pullback of `I_E^d · J'` along an open-immersion probe of the blow-up, in terms of
the pullbacks of the two factors. As in `ideal_comap_comap_of_probe`, the probe ring is
kept abstract for performance. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ)
    {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup) [IsOpenImmersion c] :
    ((((I.comap I.blowupMap) ^ d) * J').comap c).ideal ⟨⊤, isAffineOpen_top _⟩ =
      ((I.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩ ^ d *
        (J'.comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.IdealSheafData.comap_mul_of_isOpenImmersion,
    Scheme.IdealSheafData.comap_pow_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ideal_pow,
    Pi.pow_apply]

/-- The pullback of the extension of an ideal sheaf `K` on the base along a chart probe
of the blow-up: the extension of `K(V)` along the chart section map. Instantiates the
generic `ideal_comap_comap_of_probe`, which keeps the chart ring out of all rewrite
motives. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_blowupChart
    (I K : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((K.comap I.blowupMap).comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.ideal V).map (I.blowupChartSection V ha).hom :=
  Scheme.IdealSheafData.ideal_comap_comap_of_probe I K (I.blowupChart V ha) V
    (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
      (reesX (I.ideal V) a ha)))
    (I.blowupChart_comp_blowupMap V ha)

/-- On the `a`-chart of the blow-up, the pullback of the extension of the center is
generated by (the image of) `a`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_comap_blowupChart_self
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((I.comap I.blowupMap).comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(I.blowupChartSection V ha).hom a} :=
  Scheme.IdealSheafData.ideal_comap_comap_of_probe_span I I (I.blowupChart V ha) V
    (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
      (reesX (I.ideal V) a ha)))
    (I.blowupChart_comp_blowupMap V ha)
    (AffineBlowup.map_awayAlgebraMap_reesX_eq_span_singleton (I.ideal V) a ha)

/-- On the `a`-chart of the blow-up, the pullback of `I_E^d · J` is
`(a)^d · (J`-chart ideal`)`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_pow_mul_comap_blowupChart
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((((I.comap I.blowupMap) ^ d) * J').comap (I.blowupChart V ha)).ideal
        ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(I.blowupChartSection V ha).hom a} ^ d *
        (J'.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  (Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe I J' d
      (I.blowupChart V ha)).trans
    (congrArg
      (· ^ d * (J'.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩)
      (I.ideal_comap_comap_blowupChart_self V ha))

-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit.
/-- **The chart probes at a generating set cover the blow-up over `V`.** -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.preimage_subset_iUnion_range_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V) :
    (I.blowupMap ⁻¹ᵁ V.1 : Set I.blowup) ⊆
      ⋃ a : s, Set.range (I.blowupChart V (hs ▸ Ideal.subset_span a.2)) := by
  intro x hx
  have hx2 : x ∈ I.blowupMap ⁻¹ᵁ V.1 := hx
  rw [I.blowupMap_preimage V] at hx2
  obtain ⟨y, rfl⟩ := hx2
  have hy : y ∈ (⊤ : (AffineBlowup (I.ideal V)).Opens) := trivial
  rw [← AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span hs] at hy
  obtain ⟨a, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  rw [← AffineBlowup.opensRange_chart (I.ideal V)
    (reesX (I.ideal V) a.1 (hs ▸ Ideal.subset_span a.2))
    (reesX_mem (I.ideal V) a.1 (hs ▸ Ideal.subset_span a.2))] at hy
  obtain ⟨z, rfl⟩ := hy
  exact Set.mem_iUnion.mpr ⟨a, z, (Scheme.Hom.comp_apply _ _ _).symm⟩

/-- The `Opens`-level form of `preimage_subset_iUnion_range_blowupChart`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.preimage_le_iSup_opensRange_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V) :
    I.blowupMap ⁻¹ᵁ V.1 ≤
      ⨆ a : s, (I.blowupChart V (hs ▸ Ideal.subset_span a.2)).opensRange := by
  intro x hx
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (I.preimage_subset_iUnion_range_blowupChart V hs hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩

-- The chart rings of the blow-up are large `HomogeneousLocalization` types; unifying
-- them exceeds the default heartbeat limit.
/-- Precomposing the `a`-chart of the blow-up over `V` with the localization
`B_a → B_{a·b}` gives the same probe as precomposing the `b`-chart with
`B_b → B_{a·b}`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.specMap_awayMap_blowupChart
    (I : X.IdealSheafData) (V : X.affineOpens) {a b : Γ(X, V.1)} (ha : a ∈ I.ideal V)
    (hb : b ∈ I.ideal V) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) b hb) (rfl : reesX (I.ideal V) a ha * reesX (I.ideal V) b hb
          = reesX (I.ideal V) a ha * reesX (I.ideal V) b hb))) ≫ I.blowupChart V ha =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) a ha)
        (mul_comm (reesX (I.ideal V) a ha) (reesX (I.ideal V) b hb)))) ≫
        I.blowupChart V hb := by
  unfold Scheme.IdealSheafData.blowupChart AffineBlowup.chart
  rw [Proj.SpecMap_awayMap_awayι_assoc, Proj.SpecMap_awayMap_awayι_assoc]

/-- Comparing the ideals of two ideal sheaves on the image of an affine probe through
the pullbacks of global sections. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_of_comap_probe
    {Y T' : Scheme.{u}} (q : T' ⟶ Y) [IsOpenImmersion q] [IsAffine T']
    {K₁ K₂ : Y.IdealSheafData}
    (h : (K₁.comap q).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      (K₂.comap q).ideal ⟨⊤, isAffineOpen_top _⟩) :
    K₁.ideal ⟨q ''ᵁ ⊤, (isAffineOpen_top T').image_of_isOpenImmersion q⟩ ≤
      K₂.ideal ⟨q ''ᵁ ⊤, (isAffineOpen_top T').image_of_isOpenImmersion q⟩ := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h
  exact Ideal.le_of_comap_le_comap_of_bijective
    (ConcreteCategory.bijective_of_isIso _) h

/-- Comparing two ideal sheaves on affine opens inside an open `O` through their
restrictions to `O`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_ideal_of_comap_ι_le
    {Y : Scheme.{u}} {O : Y.Opens} {K₁ K₂ : Y.IdealSheafData}
    (h : K₁.comap O.ι ≤ K₂.comap O.ι) (W : Y.affineOpens) (hW : W.1 ≤ O) :
    K₁.ideal W ≤ K₂.ideal W := by
  have hle : W.1 ≤ O.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact hW
  have hW' : IsAffineOpen (O.ι ⁻¹ᵁ W.1) := W.2.preimage_of_isOpenImmersion O.ι hle
  have h' := h ⟨O.ι ⁻¹ᵁ W.1, hW'⟩
  rw [Scheme.IdealSheafData.ideal_comap_eq_map_appLE O.ι K₁ W ⟨_, hW'⟩ le_rfl,
    Scheme.IdealSheafData.ideal_comap_eq_map_appLE O.ι K₂ W ⟨_, hW'⟩ le_rfl] at h'
  haveI : IsIso (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact O.ι.isIso_app W.1 hle
  have hbij : Function.Bijective (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h2 := Ideal.comap_mono (f := (O.ι.appLE W.1 (O.ι ⁻¹ᵁ W.1) le_rfl).hom) h'
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h2

end FiniteDegreeBlowup

/-- **The affine blow-up of a finitely generated ideal is quasi-compact**: the charts at
the degree-one elements associated to a finite generating set already cover the
blow-up. -/
lemma AffineBlowup.compactSpace_of_fg {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) : CompactSpace (AffineBlowup I) := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hmem : ∀ a ∈ s, (a : A) ∈ I := fun a ha ↦ hs ▸ Ideal.subset_span ha
  have hcov : ⨆ a : s, Proj.basicOpen (reesGrading I) (reesX I a.1 (hmem a.1 a.2)) = ⊤ :=
    AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span hs
  constructor
  change IsCompact (Set.univ : Set (Proj (reesGrading I)))
  have huniv : (Set.univ : Set (Proj (reesGrading I))) =
      ⋃ a : s, (Proj.basicOpen (reesGrading I) (reesX I a.1 (hmem a.1 a.2)) : Set _) := by
    rw [← TopologicalSpace.Opens.coe_top, ← hcov]
    simp
  rw [huniv]
  refine isCompact_iUnion fun a ↦ ?_
  rw [← AffineBlowup.opensRange_chart I (reesX I a.1 (hmem a.1 a.2))
    (reesX_mem I a.1 (hmem a.1 a.2))]
  have hSpec : IsCompact (Set.univ : Set (Spec (.of (HomogeneousLocalization.Away
      (reesGrading I) (reesX I a.1 (hmem a.1 a.2)))))) := by
    have h := (isAffineOpen_top (Spec (.of (HomogeneousLocalization.Away
      (reesGrading I) (reesX I a.1 (hmem a.1 a.2)))))).isCompact
    simpa using h
  have himg := hSpec.image (AffineBlowup.chart I (reesX I a.1 (hmem a.1 a.2))
    (reesX_mem I a.1 (hmem a.1 a.2))).continuous
  rwa [Set.image_univ] at himg

/-- **The blow-up map of a finite-type ideal sheaf is quasi-compact**: the preimage of
an affine open is the affine blow-up of a finitely generated ideal. -/
lemma Scheme.IdealSheafData.quasiCompact_blowupMap {X : Scheme.{u}}
    {K : X.IdealSheafData} (hK : K.ofFiniteType) : QuasiCompact K.blowupMap := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  have h1 : K.blowupMap ⁻¹ᵁ U = (K.blowupι ⟨U, hU⟩).opensRange := K.blowupMap_preimage ⟨U, hU⟩
  rw [show (K.blowupMap ⁻¹ᵁ U : Set K.blowup) =
    ((K.blowupι ⟨U, hU⟩).opensRange : Set K.blowup) from congrArg _ h1]
  haveI := AffineBlowup.compactSpace_of_fg (hK ⟨U, hU⟩ le_top)
  exact isCompact_range (K.blowupι ⟨U, hU⟩).continuous

section LocalAlgebra

open HomogeneousLocalization Polynomial

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- Every element of the chart ring of the affine blow-up is a chart fraction
`g/aⁿ` for some degree `n` and some `g ∈ I₀ ^ n`. -/
lemma AffineBlowup.chartFrac_surjective {a : A} (ha : a ∈ I₀)
    (x : HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)) :
    ∃ (n : ℕ) (g : A) (hg : g ∈ I₀ ^ n), AffineBlowup.chartFrac I₀ ha hg = x := by
  obtain ⟨n, s, hsmem, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrading I₀) (reesX_mem I₀ a ha) x
  have hs' : s ∈ reesGrading I₀ n := by simpa using hsmem
  obtain ⟨g, hg, hrepr⟩ := (mem_reesGrading_iff_exists I₀).mp hs'
  subst hrepr
  exact ⟨n, g, hg, rfl⟩

/-- Congruence for polynomial monomials with different indices. -/
private lemma monomial_congr {i j : ℕ} {c d : A} (hij : i = j) (hcd : c = d) :
    (Polynomial.monomial i) c = (Polynomial.monomial j) d := by
  subst hij; subst hcd; rfl

/-- Clearing a power of `a` from the numerator of a chart fraction on the `b`-chart:
`(aᵏ·x)/bᵏ⁺ⁿ = (a/b)ᵏ · (x/bⁿ)`, where `a/b` is the localization element of the chart
comparison. -/
lemma AffineBlowup.chartFrac_pow_mul {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ hb hax =
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ k *
        AffineBlowup.chartFrac I₀ hb hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul, pow_one]
  exact monomial_congr (by ring) (by ring)

/-- Cancelling a power of `a` on its own chart: `(aᵏ·x)/aᵏ⁺ⁿ = x/aⁿ`. -/
lemma AffineBlowup.chartFrac_self_pow_mul {a : A} (ha : a ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ ha hax = AffineBlowup.chartFrac I₀ ha hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul]
  exact monomial_congr (by ring) (by ring)

/-- **The denominator-clearing lemma on two charts of the same Rees algebra**
(the algebraic core of Stacks Tag 0803), ring-level form: let `Ja`, `Jb` be ideals of
the `a`- and `b`-charts which agree in the common localization `B_{b·a}`. If the chart
fraction `g/aᵉ` lies in `Ja`, then multiplying `g/bᵉ` by any large enough power of the
localization element `a/b` lands in `Jb`. -/
lemma AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem
    {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    (Ja : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)))
    (Jb : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb)))
    (hab : Ja.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      Jb.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e) (hμ : AffineBlowup.chartFrac I₀ ha hg ∈ Ja) :
    ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ N' *
        AffineBlowup.chartFrac I₀ hb hg ∈ Jb := by
  set ρb := HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
    (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha) with hρb
  set t := HomogeneousLocalization.Away.isLocalizationElem
    (reesX_mem I₀ b hb) (reesX_mem I₀ a ha) with ht
  -- the image of `g/bᵉ` lies in the extension of `Jb` to the overlap
  have hmem : ρb (AffineBlowup.chartFrac I₀ hb hg) ∈ Jb.map ρb := by
    rw [hρb, AffineBlowup.awayMap_chartFrac I₀ hb ha hg, ← hab]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hμ)
  -- the overlap ring is the localization of the `b`-chart at `a/b`
  letI : Algebra
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) := ρb.toAlgebra
  haveI hloc : IsLocalization.Away t (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb * reesX I₀ a ha)) :=
    HomogeneousLocalization.Away.isLocalization_mul (reesX_mem I₀ b hb)
      (reesX_mem I₀ a ha) rfl one_ne_zero
  have halg : algebraMap
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) = ρb :=
    RingHom.algebraMap_toAlgebra ρb
  obtain ⟨N, hN⟩ := Ideal.exists_pow_mul_mem_of_algebraMap_mem_map t
    (K := Jb) (x := AffineBlowup.chartFrac I₀ hb hg) (by rw [halg]; exact hmem)
  refine ⟨N, fun N' hN' ↦ ?_⟩
  rw [← pow_sub_mul_pow t hN', mul_assoc]
  exact Ideal.mul_mem_left _ _ hN

end LocalAlgebra

section Combinators

/-- **Uniform threshold over a doubly-indexed finite family**: pointwise eventual
properties over a finite set and dependent finite sets admit a single threshold. The
index types are abstract, so all `Finset.sup` bookkeeping happens over variables and
never touches the large chart-ring types. -/
private lemma exists_uniform_ge₂ {α : Type u} (T : Finset α)
    {γ : ∀ a, a ∈ T → Type u}
    (Gf : ∀ (a : α) (ha : a ∈ T), Finset (γ a ha))
    {P : ∀ (a : α) (ha : a ∈ T) (c : γ a ha), c ∈ Gf a ha → ℕ → Prop}
    (h : ∀ a ha c hc, ∃ d₀ : ℕ, ∀ d ≥ d₀, P a ha c hc d) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ a ha c hc, P a ha c hc d := by
  classical
  choose f hf using h
  refine ⟨T.attach.sup fun a ↦ (Gf a.1 a.2).attach.sup fun c ↦ f a.1 a.2 c.1 c.2,
    fun d hd a ha c hc ↦ hf a ha c hc d (le_trans (le_trans
      (Finset.le_sup (f := fun c' ↦ f a ha c'.1 c'.2) (Finset.mem_attach _ ⟨c, hc⟩))
      (Finset.le_sup (f := fun a' : { x // x ∈ T } ↦
        (Gf a'.1 a'.2).attach.sup fun c' ↦ f a'.1 a'.2 c'.1 c'.2)
        (Finset.mem_attach _ ⟨a, ha⟩))) hd)⟩

/-- **Collection of a doubly-indexed family into a finite set**, with both the
enumeration and the membership property. The index types are abstract, so the
`Finset.biUnion`/`attach` bookkeeping happens over variables. -/
private lemma exists_finset_forall_mem {α β : Type u} (T : Finset α)
    {γ : ∀ a, a ∈ T → Type u}
    (Gf : ∀ (a : α) (ha : a ∈ T), Finset (γ a ha))
    (mf : ∀ (a : α) (ha : a ∈ T) (c : γ a ha), c ∈ Gf a ha → β) :
    ∃ M : Finset β,
      (∀ x ∈ M, ∃ (a : α) (ha : a ∈ T) (c : γ a ha) (hc : c ∈ Gf a ha),
        x = mf a ha c hc) ∧
      ∀ (a : α) (ha : a ∈ T) (c : γ a ha) (hc : c ∈ Gf a ha), mf a ha c hc ∈ M := by
  classical
  refine ⟨T.attach.biUnion fun a ↦ (Gf a.1 a.2).attach.image fun c ↦ mf a.1 a.2 c.1 c.2,
    ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨a, -, hx⟩ := hx
    rw [Finset.mem_image] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact ⟨a.1, a.2, c.1, c.2, rfl⟩
  · intro a ha c hc
    rw [Finset.mem_biUnion]
    exact ⟨⟨a, ha⟩, Finset.mem_attach _ _, Finset.mem_image.mpr
      ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩⟩

/-- Transport of an ideal membership along an equality of `CommRingCat` morphisms.
Applying this generic lemma is cheap where a `▸`-rewrite on the chart section rings
would have to abstract over the large chart types. -/
private lemma mem_of_ringHom_eq {R S : CommRingCat.{u}} {f g : R ⟶ S} (h : f = g)
    {x : R} {P : Ideal S} (hx : g.hom x ∈ P) : f.hom x ∈ P := by
  rw [h]
  exact hx

end Combinators

section ChartIdeal

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The chart model of the ideal of sections of an ideal sheaf `J` on the blow-up over
the `a`-chart: the ideal of sections of the pullback of `J` along the chart probe,
transported to the chart ring along the global-sections isomorphism. -/
def Scheme.IdealSheafData.chartIdeal (I : X.IdealSheafData) (J : I.blowup.IdealSheafData)
    (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Ideal (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha)) :=
  ((J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso _).hom.hom

/-- Membership in the chart model of `J` is membership of the transported section in
the ideal of sections of the pullback of `J`. -/
lemma Scheme.IdealSheafData.mem_chartIdeal_iff (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)}
    (ha : a ∈ I.ideal V)
    {z : HomogeneousLocalization.Away (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)} :
    z ∈ I.chartIdeal J V ha ↔ (Scheme.ΓSpecIso _).inv.hom z ∈
      (J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  have hx : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
      (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).inv.hom z) = z := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  conv_lhs => rw [← hx]
  exact CommRingCat.hom_mem_ideal_map_iso_iff _ _ _

/-- The chart model of a finite-type ideal sheaf is finitely generated. -/
lemma Scheme.IdealSheafData.chartIdeal_fg (I : X.IdealSheafData)
    {J : I.blowup.IdealSheafData} (hJ : J.ofFiniteType) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) : (I.chartIdeal J V ha).FG :=
  ((hJ.comap_of_isOpenImmersion (I.blowupChart V ha)) ⟨⊤, isAffineOpen_top _⟩ le_top).map _

/-- The chart models of `J` on two charts of the same Rees algebra agree in the common
localization `B_{b·a}`: transport of the pullback of `J` along the overlap probe. The
orientation matches the hypothesis of
`AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem`. -/
lemma Scheme.IdealSheafData.chartIdeal_map_awayMap (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a b : Γ(X, V.1)}
    (ha : a ∈ I.ideal V) (hb : b ∈ I.ideal V) :
    (I.chartIdeal J V ha).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) b hb)
        (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))) =
      (I.chartIdeal J V hb).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) a ha)
        (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
          = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)) := by
  have h1 := J.map_ideal_comap_specMap_comp (I.blowupChart V ha)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) b hb)
      (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))))
  have h2 := J.map_ideal_comap_specMap_comp (I.blowupChart V hb)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) a ha)
      (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
        = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)))
  -- the two overlap probes agree
  have hmid := congrArg
    (fun q : Spec (CommRingCat.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) b hb * reesX (I.ideal V) a ha))) ⟶ I.blowup ↦
      ((J.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso _).hom.hom)
    (I.specMap_awayMap_blowupChart V hb ha)
  exact (h1.symm.trans (hmid.symm.trans h2) :)

end ChartIdeal

section MapMembership

variable {X Y : Scheme.{u}}

/-- **Membership in the pushforward ideal through a covering family of affine probes**:
let `g : Y ⟶ X` be quasi-compact, `K` an ideal sheaf on `Y`, `V` an affine open of `X`
and `x` a section over `V`. Suppose given open-immersion probes `cᵢ : Spec Sᵢ ⟶ Y`
lying over `V` and covering `g⁻¹(V)`, such that the pullback of `x` to each probe lies
in the ideal of sections of the pullback of `K`. Then `x` lies in the ideal of the
pushforward `K.map g` over `V`. This makes the blueprint's maximal candidate
`π₎(I_E^d J)` accessible chart by chart. -/
lemma Scheme.IdealSheafData.mem_ideal_map_of_probes (K : Y.IdealSheafData)
    (g : Y ⟶ X) [QuasiCompact g] (V : X.affineOpens) (x : Γ(X, V.1))
    {ι : Type u} {S : ι → CommRingCat.{u}} (c : ∀ i, Spec (S i) ⟶ Y)
    [∀ i, IsOpenImmersion (c i)]
    (hcov : (g ⁻¹ᵁ V.1 : Set Y) ⊆ ⋃ i, Set.range (c i))
    (hle : ∀ i, (⊤ : (Spec (S i)).Opens) ≤ (c i ≫ g) ⁻¹ᵁ V.1)
    (hx : ∀ i, ((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x ∈
      (K.comap (c i)).ideal ⟨⊤, isAffineOpen_top _⟩) :
    x ∈ (K.map g).ideal V := by
  haveI : QuasiCompact (K.subschemeι ≫ g) := inferInstance
  change x ∈ (K.subschemeι ≫ g).ker.ideal V
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  apply K.subscheme.IsSheaf.section_ext
  intro p hp
  -- the image of `p` in `Y` lies over `V`, hence in the range of some probe
  have hpV : K.subschemeι p ∈ (g ⁻¹ᵁ V.1 : Set Y) := by
    change g (K.subschemeι p) ∈ V.1
    rw [← Scheme.Hom.comp_apply]
    exact hp
  obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hcov hpV
  -- the pullback of the probe to the subscheme
  haveI : IsClosedImmersion (pullback.fst (c i) K.subschemeι) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hprange : p ∈ Set.range (pullback.snd (c i) K.subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hy⟩
  obtain ⟨q, hq⟩ := hprange
  -- the composite of the pullback square with the probe
  have hcomp : pullback.snd (c i) K.subschemeι ≫ K.subschemeι ≫ g =
      pullback.fst (c i) K.subschemeι ≫ (c i ≫ g) := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
  -- the witnessing open: the image of the preimage of `(subschemeι ≫ g)⁻¹(V)`
  refine ⟨pullback.snd (c i) K.subschemeι ''ᵁ
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)), ?_,
    ⟨q, ?_, hq⟩, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hw
  · change pullback.snd (c i) K.subschemeι q ∈ (K.subschemeι ≫ g) ⁻¹ᵁ V.1
    rw [hq]
    exact hp
  -- both restrictions are computed by pulling back to the probe
  rw [map_zero]
  apply ((pullback.snd (c i) K.subschemeι).appIso
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
      ).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  -- exchange the composite for the probe composite and split off the probe map
  rw [Scheme.Hom.appLE_eq_of_eq hcomp]
  rw [← Scheme.Hom.appLE_comp_appLE (pullback.fst (c i) K.subschemeι) (c i ≫ g)
    V.1 ⊤ (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
    (hle i) le_top]
  rw [CommRingCat.comp_apply]
  -- the probe image of `x` is killed by the closed immersion from the subscheme part
  have h0 : ((pullback.fst (c i) K.subschemeι).app ⊤).hom
      (((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x) = 0 := by
    apply Scheme.Hom.ideal_ker_le _ ⟨⊤, isAffineOpen_top _⟩
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
    exact hx i
  have hexp : (pullback.fst (c i) K.subschemeι).appLE ⊤
      (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)) le_top =
      (pullback.fst (c i) K.subschemeι).app ⊤ ≫
        (Limits.pullback (c i) K.subschemeι).presheaf.map (homOfLE le_top).op := rfl
  rw [hexp, CommRingCat.comp_apply, h0, map_zero]

end MapMembership

section UniformNumerator

open HomogeneousLocalization

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- **The uniform numerator construction** (Steps 2–3 of the blueprint proof of Stacks
Tag 0803, ring-level form): given a finite generating set `s` of `I₀`, a family of
chart ideals `Jc` agreeing on overlaps, and a chart fraction `g/aᵉ` lying in the chart
ideal of the `a`-chart, there is a threshold `d₀` such that for every `d ≥ d₀` there is
a numerator `m ∈ I₀ᵈ` with `m/aᵈ = g/aᵉ` on the `a`-chart whose fraction `m/bᵈ` lies in
the chart ideal of every `b`-chart, `b ∈ s`. -/
lemma AffineBlowup.exists_uniform_numerator
    (s : Finset A) (hs : Ideal.span (s : Set A) = I₀)
    (Jc : ∀ (b : A) (hb : b ∈ I₀), Ideal (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hJc : ∀ (a b : A) (ha : a ∈ I₀) (hb : b ∈ I₀),
      (Jc a ha).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      (Jc b hb).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {a : A} (has : a ∈ s) {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e)
    (hμ : AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg ∈
      Jc a (hs ▸ Ideal.subset_span has)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : A) (hm : m ∈ I₀ ^ d),
      AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) m =
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg *
          AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) a ^ d ∧
      ∀ (b : A) (hbs : b ∈ s), AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hm ∈
        Jc b (hs ▸ Ideal.subset_span hbs) := by
  classical
  have ha' : a ∈ I₀ := hs ▸ Ideal.subset_span has
  -- clearing exponents for each chart in the generating set
  have hclear : ∀ (b : A) (hbs : b ∈ s), ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem
          (reesX_mem I₀ b (hs ▸ Ideal.subset_span hbs)) (reesX_mem I₀ a ha') ^ N' *
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hg ∈
      Jc b (hs ▸ Ideal.subset_span hbs) := fun b hbs ↦
    AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem I₀ ha'
      (hs ▸ Ideal.subset_span hbs) (Jc a ha') (Jc b (hs ▸ Ideal.subset_span hbs))
      (hJc a b ha' (hs ▸ Ideal.subset_span hbs)) hg hμ
  choose N hN using hclear
  refine ⟨(s.attach.sup fun b ↦ N b.1 b.2) + e, fun d hd ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + e := ⟨d - e, by omega⟩
  have hkN : ∀ (b : A) (hbs : b ∈ s), N b hbs ≤ k := by
    intro b hbs
    have h1 : N b hbs ≤ s.attach.sup fun b ↦ N b.1 b.2 :=
      Finset.le_sup (f := fun b : { x // x ∈ s } ↦ N b.1 b.2)
        (Finset.mem_attach _ ⟨b, hbs⟩)
    omega
  have hm : a ^ k * g ∈ I₀ ^ (k + e) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ha' k) hg
  refine ⟨a ^ k * g, hm, ?_, ?_⟩
  · rw [← AffineBlowup.chartFrac_mul_awayAlgebraMap_pow I₀ ha' hm,
      AffineBlowup.chartFrac_self_pow_mul I₀ ha' hg hm]
  · intro b hbs
    rw [AffineBlowup.chartFrac_pow_mul I₀ ha' (hs ▸ Ideal.subset_span hbs) hg hm]
    exact hN b hbs k (hkN b hbs)

/-- **The uniform numerator finset** (Steps 2–4 of the blueprint proof of Stacks
Tag 0803, ring-level form): given a finite generating set `s` of `I₀` and a compatible
family of chart ideals `Jc` with finite generating sets `G`, there is a threshold `d₀`
such that for every `d ≥ d₀` there is a finite set `M ⊆ I₀ᵈ` of numerators whose chart
fractions `m/bᵈ` lie in every chart ideal, and which clear every generator of every
chart ideal: `μ · (b/1)ᵈ = m/1` on the `b`-chart. All indexing over the generating
sets happens here, over an abstract ring, keeping the `Finset` bookkeeping away from
the section rings of schemes. -/
lemma AffineBlowup.exists_uniform_numerator_finset
    (s : Finset A) (hs : Ideal.span (s : Set A) = I₀)
    (Jc : ∀ (b : A) (hb : b ∈ I₀), Ideal (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hJc : ∀ (a b : A) (ha : a ∈ I₀) (hb : b ∈ I₀),
      (Jc a ha).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      (Jc b hb).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    (G : ∀ (b : A) (hb : b ∈ I₀), Finset (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hG : ∀ (b : A) (hb : b ∈ I₀), Ideal.span (G b hb : Set _) = Jc b hb) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ M : Finset A,
      (∀ m ∈ M, ∃ hm : m ∈ I₀ ^ d, ∀ (b : A) (hbs : b ∈ s),
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hm ∈
          Jc b (hs ▸ Ideal.subset_span hbs)) ∧
      ∀ (b : A) (hbs : b ∈ s), ∀ μ ∈ G b (hs ▸ Ideal.subset_span hbs),
        ∃ m ∈ M,
          μ * AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) b
              ^ d =
            AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) m := by
  classical
  -- numerator thresholds for every chart generator
  have hnum : ∀ (b : A) (hbs : b ∈ s)
      (μ : HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b (hs ▸ Ideal.subset_span hbs)))
      (_ : μ ∈ G b (hs ▸ Ideal.subset_span hbs)),
      ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : A) (hm : m ∈ I₀ ^ d),
        AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) m =
          μ * AffineBlowup.awayAlgebraMap I₀ (reesX I₀ b (hs ▸ Ideal.subset_span hbs)) b
            ^ d ∧
        ∀ (b' : A) (hbs' : b' ∈ s),
          AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs') hm ∈
            Jc b' (hs ▸ Ideal.subset_span hbs') := by
    intro b hbs μ hμG
    obtain ⟨e, g, hg, rfl⟩ := AffineBlowup.chartFrac_surjective I₀
      (hs ▸ Ideal.subset_span hbs) μ
    exact AffineBlowup.exists_uniform_numerator I₀ s hs Jc hJc hbs hg
      ((hG b (hs ▸ Ideal.subset_span hbs)) ▸ Ideal.subset_span hμG)
  -- one uniform threshold, by the abstract double-sup combinator
  obtain ⟨d₀, hd₀⟩ := exists_uniform_ge₂ s
    (fun b hbs ↦ G b (hs ▸ Ideal.subset_span hbs)) hnum
  refine ⟨d₀, fun d hd ↦ ?_⟩
  -- the numerators at degree `d`, collected into a finite set
  choose mf hmI hrest using hd₀ d hd
  obtain ⟨M, hM₁, hM₂⟩ := exists_finset_forall_mem s
    (fun b hbs ↦ G b (hs ▸ Ideal.subset_span hbs)) mf
  refine ⟨M, ?_, ?_⟩
  · intro m hmM
    obtain ⟨b, hbs, μ, hμG, rfl⟩ := hM₁ m hmM
    exact ⟨hmI b hbs μ hμG, (hrest b hbs μ hμG).2⟩
  · intro b hbs μ hμG
    exact ⟨mf b hbs μ hμG, hM₂ b hbs μ hμG, (hrest b hbs μ hμG).1.symm⟩

end UniformNumerator

section ChartMembership

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The image of a factored element under a ring homomorphism, commuted into the shape
of a power times a factor. Keeping the rings abstract makes this cheap to instantiate
at the section rings of blow-up charts. -/
private lemma ringHom_pow_mul_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {x y z : R} (d : ℕ) (h : y * x ^ d = z) :
    (f x) ^ d * f y = f z := by
  rw [← h, map_mul, map_pow, mul_comm]

/-- **Membership criterion for the pullback of `I_Eᵈ · J'` along an open-immersion
probe**, generic in the probe ring: an element factoring as `yPᵈ · yQ` with `yP` in the
pulled-back exceptional ideal and `yQ` in the pulled-back `J'` lies in the pullback of
the product. -/
lemma Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ)
    {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup) [IsOpenImmersion c]
    {x yP yQ : Γ(Spec S, ⊤)}
    (hP : yP ∈ ((I.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hQ : yQ ∈ (J'.comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hx : yP ^ d * yQ = x) :
    x ∈ ((((I.comap I.blowupMap) ^ d) * J').comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe I J' d c, ← hx]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hP d) hQ

/-- If the chart fraction `m/bᵈ` of a section `m ∈ I(V)ᵈ` lies in the chart model of
`J`, then the chart image of `m` lies in the ideal of sections of the pullback of
`I_Eᵈ · J` on the `b`-chart. This is the membership input both for the pushforward
candidate and for the final generation argument. -/
lemma Scheme.IdealSheafData.blowupChartSection_mem_of_chartFrac_mem
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (V : X.affineOpens)
    {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) {d : ℕ}
    {m : Γ(X, V.1)} (hm : m ∈ (I.ideal V) ^ d)
    (hfrac : AffineBlowup.chartFrac (I.ideal V) hb hm ∈ I.chartIdeal J V hb) :
    (I.blowupChartSection V hb).hom m ∈
      ((((I.comap I.blowupMap) ^ d) * J).comap (I.blowupChart V hb)).ideal
        ⟨⊤, isAffineOpen_top _⟩ :=
  Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe I J d (I.blowupChart V hb)
    ((I.ideal_comap_comap_blowupChart_self V hb).ge (Ideal.subset_span rfl))
    ((I.mem_chartIdeal_iff J V hb).mp hfrac)
    (ringHom_pow_mul_eq
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) b hb)))).inv.hom d
      (AffineBlowup.chartFrac_mul_awayAlgebraMap_pow (I.ideal V) hb hm))

end ChartMembership

section Generation

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- Transport of a generating set along an isomorphism of `CommRingCat`. -/
private lemma span_eq_of_map_iso_span {R S : CommRingCat.{u}} (E : R ≅ S)
    {P : Ideal R} {G : Set S} (h : Ideal.span G = P.map E.hom.hom) :
    P = Ideal.span (E.inv.hom '' G) := by
  have h1 := congrArg (Ideal.map E.inv.hom) h
  rw [Ideal.map_span, Ideal.map_map, ← CommRingCat.hom_comp, E.hom_inv_id,
    CommRingCat.hom_id, Ideal.map_id] at h1
  exact h1.symm

/-- **The generation step of Stacks Tag 0803**, ring-level form: if every generator
`μ` of an ideal spanned by `e '' G` satisfies `μ · f(b)ᵈ = f(m)` for some `m` in an
ideal `K` of the base ring, then `(g b)ᵈ · span (e '' G)` is contained in the
extension of `K` along the composite `g` of `f` and `e`. -/
private lemma span_pow_mul_span_le_map_explicit
    {A B C : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (K : Ideal A)
    (f : A →+* B)
    (e : B →+* C)
    (g : A →+* C)
    (hcomp : ∀ x : A, e (f x) = g x)
    (b : A) (d : ℕ) (G : Set B)
    (hgen : ∀ μ ∈ G, ∃ m ∈ K,
      μ * f b ^ d = f m) :
    Ideal.span {g b} ^ d * Ideal.span (e '' G) ≤ Ideal.map g K := by
  rw [Ideal.span_singleton_pow, Ideal.span_mul_span]
  refine Ideal.span_le.2 ?_
  intro z hz
  rcases Set.mem_mul.mp hz with ⟨x, hx, y, hy, hxy⟩
  have hx' : x = g b ^ d := by
    simpa only [Set.mem_singleton_iff] using hx
  subst x
  rcases hy with ⟨μ, hμ, hy⟩
  subst y
  rcases hgen μ hμ with ⟨m, hmK, hm⟩
  have heq : g b ^ d * e μ = g m := by
    calc
      g b ^ d * e μ
          = e (f b) ^ d * e μ := by
              rw [← hcomp b]
      _ = e (f b ^ d) * e μ := by
              rw [map_pow]
      _ = e (f b ^ d * μ) := by
              rw [map_mul]
      _ = e (μ * f b ^ d) := by
              rw [mul_comm (f b ^ d) μ]
      _ = e (f m) := by
              rw [hm]
      _ = g m := hcomp m
  rw [← hxy, heq]
  exact Ideal.mem_map_of_mem g hmK

/-- **The chartwise generation inequality** (Step 4 of the blueprint proof of Stacks
Tag 0803): if every generator of the chart model of `J` on the `b`-chart has a
numerator in `L(V)`, then the ideal of `I_Eᵈ · J` on the chart is contained in that of
the inverse image of `L`. -/
lemma Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (L : X.IdealSheafData)
    (V : X.affineOpens) {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) (d : ℕ)
    (G : Finset (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) b hb)))
    (hG : Ideal.span (G : Set _) = I.chartIdeal J V hb)
    (hgen : ∀ μ ∈ G, ∃ m' ∈ L.ideal V,
      μ * AffineBlowup.awayAlgebraMap
          (I.ideal V) (reesX (I.ideal V) b hb) b ^ d =
        AffineBlowup.awayAlgebraMap
          (I.ideal V) (reesX (I.ideal V) b hb) m') :
    (((I.comap I.blowupMap) ^ d) * J).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ ≤
      (L.comap I.blowupMap).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤,
          (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
  apply Scheme.IdealSheafData.ideal_le_of_comap_probe
    (I.blowupChart V hb)
  refine le_of_eq_of_le
    (Scheme.IdealSheafData.ideal_comap_pow_mul_comap_blowupChart
      I J d V hb) ?_
  refine le_of_le_of_eq ?_
    (Scheme.IdealSheafData.ideal_comap_comap_blowupChart
      I L V hb).symm
  refine le_of_eq_of_le
    (congrArg
      (fun Q ↦
        Ideal.span {(I.blowupChartSection V hb).hom b} ^ d * Q)
      (span_eq_of_map_iso_span
        (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away
              (reesGrading (I.ideal V))
              (reesX (I.ideal V) b hb))))
        hG)) ?_
  apply span_pow_mul_span_le_map_explicit
    (K := L.ideal V)
    (f :=
      AffineBlowup.awayAlgebraMap
        (I.ideal V) (reesX (I.ideal V) b hb))
    (e :=
      (Scheme.ΓSpecIso
        (CommRingCat.of
          (HomogeneousLocalization.Away
            (reesGrading (I.ideal V))
            (reesX (I.ideal V) b hb)))).inv.hom)
    (g := (I.blowupChartSection V hb).hom)
    (b := b)
    (d := d)
    (G := (G : Set _))
  · intro x
    rfl
  · intro μ hμ
    exact hgen μ hμ

end Generation

section Main

variable {X : Scheme.{u}}

/-- Pullback of a finite supremum of ideal sheaves. -/
private lemma comap_finset_sup {Y : Scheme.{u}} {α : Type*} (T : Finset α)
    (F : α → X.IdealSheafData) (f : Y ⟶ X) :
    (T.sup F).comap f = T.sup fun a ↦ (F a).comap f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T' ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih]

/-- The bottom ideal sheaf is of finite type. -/
private lemma finiteType_bot : (⊥ : X.IdealSheafData).ofFiniteType := fun U _ ↦ by
  have h : (⊥ : X.IdealSheafData).ideal U = ⊥ :=
    congrFun Scheme.IdealSheafData.ideal_bot U
  rw [h]
  exact Submodule.fg_bot

/-- **Membership of a numerator in the maximal candidate** (pushforward part): if all
chart fractions of a section `m ∈ I(V)ᵈ` lie in the chart models of `J`, then `m` is a
section of the pushforward of `I_Eᵈ · J`. -/
lemma Scheme.IdealSheafData.mem_ideal_map_pow_mul_of_chartFrac_mem
    (I : X.IdealSheafData) [QuasiCompact I.blowupMap] (J : I.blowup.IdealSheafData)
    (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V)
    {d : ℕ} {m : Γ(X, V.1)} (hm : m ∈ (I.ideal V) ^ d)
    (hchart : ∀ (b : Γ(X, V.1)) (hbs : b ∈ s),
      AffineBlowup.chartFrac (I.ideal V) (hs ▸ Ideal.subset_span hbs) hm ∈
        I.chartIdeal J V (hs ▸ Ideal.subset_span hbs)) :
    m ∈ (((I.comap I.blowupMap) ^ d * J).map I.blowupMap).ideal V := by
  refine Scheme.IdealSheafData.mem_ideal_map_of_probes _ I.blowupMap V m
    (c := fun b' : ↥s ↦ I.blowupChart V (hs ▸ Ideal.subset_span b'.2))
    (I.preimage_subset_iUnion_range_blowupChart V hs)
    (fun b' ↦ I.blowupChart_comp_blowupMap_preimage V (hs ▸ Ideal.subset_span b'.2)) ?_
  intro b'
  exact mem_of_ringHom_eq
    (I.appLE_blowupChart_comp_blowupMap V (hs ▸ Ideal.subset_span b'.2)
      (I.blowupChart_comp_blowupMap_preimage V (hs ▸ Ideal.subset_span b'.2)))
    (I.blowupChartSection_mem_of_chartFrac_mem J V (hs ▸ Ideal.subset_span b'.2) hm
      (hchart b'.1 b'.2))

/-- **The chart images at a finite affine cover of the base cover the blow-up.** -/
lemma Scheme.IdealSheafData.iSup_blowupChart_image_top_eq_top
    (I : X.IdealSheafData) {t : Finset X.affineOpens}
    (ht : Set.univ ⊆ ⋃ V ∈ t, (V.1 : Set X))
    (s : ∀ V : X.affineOpens, Finset Γ(X, V.1))
    (hs : ∀ V : X.affineOpens, Ideal.span (s V : Set Γ(X, V.1)) = I.ideal V) :
    (⨆ p : Σ V : { V // V ∈ t }, { b // b ∈ s V.1 },
      I.blowupChart p.1.1 ((hs p.1.1) ▸ Ideal.subset_span p.2.2) ''ᵁ ⊤) = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : I.blowup.Opens) ≤ ⨆ V : { V // V ∈ t }, I.blowupMap ⁻¹ᵁ V.1.1 := by
    intro x _
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (I.blowupMap x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVt⟩, hxV⟩
  refine le_trans h1 (iSup_le fun V ↦ ?_)
  refine le_trans (I.preimage_le_iSup_opensRange_blowupChart V.1 (hs V.1))
    (iSup_le fun b ↦ le_iSup_of_le ⟨V, b⟩ ?_)
  intro x hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, trivial, hz⟩

/-- **Finite-degree approximation on the blow-up itself** (Stacks Project Tag 0803):
for finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there
are `d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is
`I_E^d · J`. The candidate for `L` at degree `d` is a finite-type subsheaf of
`(I^d) ⊓ ((I_E^d * J).map I.blowupMap)` through the finitely many chart numerators of
`AffineBlowup.exists_uniform_numerator_finset`, which generate `I_E^d · J` chart by
chart for `d` large.
(Blueprint: `lemma:nagata-proj-closed-center-finite-degree-exists`.) -/
theorem Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.ofFiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.ofFiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), 0 < d ∧ L.ofFiniteType ∧ L ≤ I ^ d ∧
      L.comap I.blowupMap = (I.comap I.blowupMap) ^ d * J := by
  classical
  haveI : QuasiCompact I.blowupMap := Scheme.IdealSheafData.quasiCompact_blowupMap hI
  -- a finite affine cover of `X`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- generators of the center over each affine open
  choose s hs using fun V : X.affineOpens ↦ hI V le_top
  -- generators of the chart models of `J`
  choose G hG using fun (V : X.affineOpens) (b : Γ(X, V.1)) (hb : b ∈ I.ideal V) ↦
    I.chartIdeal_fg hJ V hb
  -- per-cover-member uniform thresholds and numerator finsets, at the ring level
  choose d₀f hd₀f using fun V : X.affineOpens ↦
    AffineBlowup.exists_uniform_numerator_finset (I.ideal V) (s V) (hs V)
      (fun b hb ↦ I.chartIdeal J V hb)
      (fun a b ha hb ↦ I.chartIdeal_map_awayMap J V ha hb)
      (G V) (fun b hb ↦ hG V b hb)
  -- one global degree dominating all thresholds
  refine ⟨1 + t.sup d₀f, ?_⟩
  set D : ℕ := 1 + t.sup d₀f with hD
  -- the numerator finsets at the global degree
  choose M hM₁ hM₂ using fun (V : X.affineOpens) (hVt : V ∈ t) ↦
    hd₀f V D (le_trans (Finset.le_sup hVt) (Nat.le_add_left _ 1))
  -- membership of the numerators in the maximal candidate
  have hmC : ∀ (V : X.affineOpens) (hVt : V ∈ t), ∀ m ∈ M V hVt,
      m ∈ (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)).ideal V := by
    intro V hVt m hmM
    obtain ⟨hmI, hchart⟩ := hM₁ V hVt m hmM
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : (I ^ D).ideal V = (I.ideal V) ^ D := by
        rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact heq.ge hmI
    · exact I.mem_ideal_map_pow_mul_of_chartFrac_mem J V (hs V) hmI hchart
  -- extraction of a finite-type subsheaf through the numerators, per cover member
  have hLV : ∀ (V : X.affineOpens), V ∈ t → ∃ LV : X.IdealSheafData,
      LV ≤ I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap) ∧
      LV.ofFiniteType ∧ ∀ (hVt : V ∈ t),
        LV.ideal V = Ideal.span (M V hVt : Set Γ(X, V.1)) := by
    intro V hVt
    obtain ⟨LV, h1, h2, h3⟩ := Scheme.IdealSheafData.exists_finiteType_le_ideal_eq
      (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)) V
      (F := Ideal.span (M V hVt : Set Γ(X, V.1)))
      ⟨_, rfl⟩ (by
        rw [Ideal.span_le]
        intro x hx
        exact hmC V hVt x (Finset.mem_coe.mp hx))
    exact ⟨LV, h1, h2, fun _ ↦ h3⟩
  choose LV hLVle hLVft hLVid using hLV
  refine ⟨t.attach.sup fun V ↦ LV V.1 V.2,
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _), ?_, ?_, ?_⟩
  · -- finite type: finite supremum of finite-type subsheaves
    exact Finset.sup_induction finiteType_bot
      (fun _ ha _ hb ↦ Scheme.IdealSheafData.ofFiniteType.sup ha hb)
      fun V _ ↦ hLVft V.1 V.2
  · -- contained in `I ^ D`
    exact Finset.sup_le fun V _ ↦ (hLVle V.1 V.2).trans inf_le_left
  · -- the inverse image ideal is `I_E^D · J`
    apply le_antisymm
    · -- `≤`: from the pushforward bound, by the Galois connection
      rw [comap_finset_sup]
      refine Finset.sup_le fun V _ ↦ ?_
      have h1 : LV V.1 V.2 ≤ ((I.comap I.blowupMap) ^ D * J).map I.blowupMap :=
        (hLVle V.1 V.2).trans inf_le_right
      exact ((Scheme.IdealSheafData.comap_mono I.blowupMap) h1).trans
        (Scheme.IdealSheafData.comap_map_le _ _)
    · -- `≥`: chartwise generation by the numerators
      refine Scheme.IdealSheafData.le_of_iSup_eq_top
        (fun p : Σ V : { V // V ∈ t }, { b // b ∈ s V.1 } ↦
          ⟨I.blowupChart p.1.1 ((hs p.1.1) ▸ Ideal.subset_span p.2.2) ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩) ?_ ?_
      · -- the chart images cover the blow-up
        exact I.iSup_blowupChart_image_top_eq_top ht s hs
      · -- the generation inequality on each chart
        rintro ⟨⟨V, hVt⟩, b'⟩
        refine Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators I J _ V
          ((hs V) ▸ Ideal.subset_span b'.2) D
          (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2))
          (hG V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)) ?_
        intro μ0 hμ0
        obtain ⟨m0, hm0M, heq⟩ := hM₂ V hVt b'.1 b'.2 μ0 hμ0
        refine ⟨m0, ?_, heq⟩
        have h1 : m0 ∈ (LV V hVt).ideal V := by
          rw [hLVid V hVt hVt]
          exact Ideal.subset_span (Finset.mem_coe.mpr hm0M)
        have h2 : LV V hVt ≤ t.attach.sup fun V' ↦ LV V'.1 V'.2 :=
          Finset.le_sup (f := fun V' : { x // x ∈ t } ↦ LV V'.1 V'.2)
            (Finset.mem_attach _ ⟨V, hVt⟩)
        exact h2 V h1

end Main

end AlgebraicGeometry
