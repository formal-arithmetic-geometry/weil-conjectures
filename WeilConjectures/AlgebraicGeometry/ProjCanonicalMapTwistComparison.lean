/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso
import WeilConjectures.AlgebraicGeometry.NonvanishingGeneratingLocus

/-!
# Sufficiently divisible twists pull back to powers of the line module

Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme.Modules

/-- The homogeneous section of the invertible section ring determined by a graded map.
Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison). -/
noncomputable def gradedSectionElement {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M) {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    sectionRingGrade M n :=
  ⟨ψ.toRingHom a, ψ.map_mem ha⟩

/-- The graded section-ring element has the prescribed homogeneous degree.
Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison). -/
@[simp] theorem gradedSectionElement_val {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    {Z : Scheme.{u}} (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M) {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) :
    (gradedSectionElement 𝒜 M ψ a ha).val = ψ.toRingHom a :=
  by rfl

private theorem tensorPullbackSection_transport {X Y : Scheme.{u}} (r : X ⟶ Y)
    (N : Y.Modules) (U : Y.Opens) (s : Γ(N, U)) :
    (((tensorPullbackSectionAdjunction r).leftAdjointUniq
      (pullbackPushforwardAdjunction r)).app N).hom.app (r ⁻¹ᵁ U)
        (tensorPullbackSection r N U s) = pullbackSection r s := by
  have hn : ((tensorPullbackSectionAdjunction r).unit.app N).app U s =
      tensorPullbackSection r N U s :=
    (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction r)).1 N U s
  rw [← hn]
  have h := (tensorPullbackSectionAdjunction r).unit_leftAdjointUniq_hom_app
    (pullbackPushforwardAdjunction r) N
  exact congrArg (fun f ↦ f.app U s) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_common_degree_cover {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (Z : Scheme.{u}) [CompactSpace Z] (r : Z ⟶ Proj 𝒜)
    (hcover : ∀ z : Z, ∃ (n : ℕ) (a : A), a ∈ 𝒜 n ∧
      0 < n ∧ z ∈ r ⁻¹ᵁ Proj.basicOpen 𝒜 a) :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ, 0 < k →
      (⨆ a : 𝒜 (d * k), r ⁻¹ᵁ Proj.basicOpen 𝒜 a.val) = ⊤ := by
  classical
  choose n a ha hn hz using hcover
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z ↦ (r ⁻¹ᵁ Proj.basicOpen 𝒜 (a z) : Set Z))
    (fun z ↦ (r ⁻¹ᵁ Proj.basicOpen 𝒜 (a z)).isOpen)
    (fun z _ ↦ Set.mem_iUnion.mpr ⟨z, hz z⟩)
  let d := ∏ z ∈ t, n z
  have hd : 0 < d := Finset.prod_pos (fun z _ ↦ hn z)
  refine ⟨d, hd, fun k hk ↦ eq_top_iff.mpr ?_⟩
  intro z _
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  have hdiv : n w ∣ d * k :=
    dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem n hw) k
  have hq : 0 < d * k / n w :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hd hk) hdiv) (hn w)
  have hpow : a w ^ (d * k / n w) ∈ 𝒜 (d * k) := by
    have h := SetLike.pow_mem_graded (d * k / n w) (ha w)
    simpa only [smul_eq_mul, Nat.div_mul_cancel hdiv] using h
  apply Opens.mem_iSup.mpr
  refine ⟨⟨a w ^ (d * k / n w), hpow⟩, ?_⟩
  change r z ∈ Proj.basicOpen 𝒜 (a w ^ (d * k / n w))
  rw [Proj.basicOpen_pow 𝒜 _ _ hq]
  exact hzw

private theorem exists_iso_of_section_ratios {X : Scheme.{u}} {P Q : X.Modules}
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (s : ι → Γ(P, ⊤)) (t : ι → Γ(Q, ⊤))
    (hs : ∀ i, IsFreeGenerator (P.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)))
    (ht : ∀ i, IsFreeGenerator (Q.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (t i)))
    (hr : ∀ i j, ∃ c : Γ(X, U j),
      P.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s i) =
        c • P.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (s j) ∧
      Q.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (t i) =
        c • Q.presheaf.map (homOfLE (le_top : U j ≤ ⊤)).op (t j)) :
    ∃ e : P ≅ Q, ∀ i, e.hom.app ⊤ (s i) = t i := by
  let e i := P.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (s i)
  let f i := Q.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (t i)
  have hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
      a • P.presheaf.map (homOfLE hi).op (e i) =
        b • P.presheaf.map (homOfLE hj).op (e j) →
      a • Q.presheaf.map (homOfLE hi).op (f i) =
        b • Q.presheaf.map (homOfLE hj).op (f j) := by
    intro i j W hi hj a b hab
    obtain ⟨c, hcs, hct⟩ := hr i j
    have hcs' := presheaf_map_homOfLE_eq_smul (le_top : U j ≤ ⊤) hj hcs
    have hct' := presheaf_map_homOfLE_eq_smul (le_top : U j ≤ ⊤) hj hct
    dsimp only [e, f] at hab ⊢
    simp only [presheaf_map_homOfLE_map_homOfLE] at hab ⊢
    rw [hcs', smul_smul] at hab
    have hsj := (hs j).map hj
    simp only [presheaf_map_homOfLE_map_homOfLE] at hsj
    have hab' := hsj.smul_left_injective hab
    rw [hct', smul_smul]
    exact congrArg (fun c ↦ c • Q.presheaf.map (homOfLE le_top).op (t j)) hab'
  let q := isoOfIsFreeGenerator hU hs ht hc
  refine ⟨q, fun i ↦ ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨Q.presheaf, Q.isSheaf⟩ U ⊤
    (fun _ ↦ homOfLE le_top) (fun x _ ↦ hU.ge (Set.mem_univ x))
  intro j
  obtain ⟨c, hcs, hct⟩ := hr i j
  rw [← Hom.app_presheaf_map, hcs, hct]
  simpa only [presheaf_map_id_apply] using
    isoOfIsFreeGenerator_hom_app_smul hU hs ht hc j le_rfl c

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- For a graded section-ring map whose positive-degree nonvanishing opens cover a
quasi-compact scheme, the canonical Proj morphism pulls back a sufficiently divisible
twist to the corresponding tensor power of the invertible module. Each isomorphism
is normalized by sending the actual tensor pullback of every homogeneous degree-`d * k`
section to its image under `ψ`, as in the commutative diagram of Tag 01NK.

Source: Stacks Project, `constructions.tex`, Tags 01NK and 01N8
(blueprint: lem-trf-proj-canonical-map-twist-comparison).

Proof: Apply the canonical generation-locus construction to the graded map and identify its
positive-degree locus with all of `Z`.  Quasi-compactness gives finitely many positive-degree
homogeneous sections; taking a common positive multiple `d` makes the degree-`d` sections
and all their positive multiples generate the corresponding tensor powers.  The generated-chart
comparison gives the canonical isomorphism on each degree `d * k`; the uniqueness clause makes
these comparisons independent of the finite subcover and common multiple. The normalization
is the equality on homogeneous sections in property (2) of Tag 01NK: `unitToTwist` is the
section `a/1`, `tensorPullbackSection` is its actual pullback `1 ⊗ a`, and the comparison
sends this to `ψ(a)`. For an empty scheme,
`d = 1` is allowed and all comparison assertions are vacuous. -/
theorem exists_proj_canonical_map_twist_comparison
    {A : Type u} [CommRing A]
    (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (Z : Scheme.{u}) [CompactSpace Z] (M : Z.Modules) [M.IsInvertible]
    (ψ : 𝒜 →+*ᵍ sectionRingGrade M)
    (hcover : ∀ z : Z, ∃ (n : ℕ) (a : A) (ha : a ∈ 𝒜 n),
      0 < n ∧ z ∈ nonvanishingLocus (M.tensorPow n)
        ((gradedSectionElement 𝒜 M ψ a ha).val n))
    (r : Z ⟶ Proj 𝒜)
    (hr_preimage : ∀ (d : ℕ) (_hd : 0 < d) (a : A) (ha : a ∈ 𝒜 d),
      (r ⁻¹ᵁ Proj.basicOpen 𝒜 a : Set Z) =
        nonvanishingLocus (M.tensorPow d)
          ((gradedSectionElement 𝒜 M ψ a ha).val d))
    (hr_formula : ∀ (d : ℕ) (_hd : 0 < d) (a : A) (ha : a ∈ 𝒜 d),
      ∀ (n : ℕ) (b : A) (hb : b ∈ 𝒜 (n • d)),
        (r.app (Proj.basicOpen 𝒜 a)
          (Proj.awayToSection 𝒜 a
            (HomogeneousLocalization.Away.mk 𝒜 ha n b hb))) •
            (M.tensorPow (n • d)).presheaf.map
              (homOfLE (le_top : r ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
              (((gradedSectionElement 𝒜 M ψ a ha).val ^ n) (n • d)) =
          (M.tensorPow (n • d)).presheaf.map
            (homOfLE (le_top : r ⁻¹ᵁ Proj.basicOpen 𝒜 a ≤ ⊤)).op
            ((gradedSectionElement 𝒜 M ψ b hb).val (n • d))) :
    ∃ d : ℕ, 0 < d ∧
      ∀ k : ℕ, 0 < k →
        ∃ θ : ((tensorPullback r).obj (Proj.twist 𝒜 (0 + ((d * k : ℕ) : ℤ))) ≅
          M.tensorPow (d * k)),
          ∀ (a : A) (ha : a ∈ 𝒜 (d * k)),
            θ.hom.app (r ⁻¹ᵁ ⊤)
                (tensorPullbackSection r (Proj.twist 𝒜 (0 + ((d * k : ℕ) : ℤ))) ⊤
                  ((Proj.unitToTwist (𝒜 := 𝒜) ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤)))) =
              (M.tensorPow (d * k)).presheaf.map
                (homOfLE (le_top : r ⁻¹ᵁ ⊤ ≤ ⊤)).op
                ((gradedSectionElement 𝒜 M ψ a ha).val (d * k)) := by
  classical
  obtain ⟨d, hd, hcov⟩ := exists_common_degree_cover 𝒜 Z r (by
    intro z
    obtain ⟨n, a, ha, hn, hz⟩ := hcover z
    refine ⟨n, a, ha, hn, ?_⟩
    change z ∈ (r ⁻¹ᵁ Proj.basicOpen 𝒜 a : Set Z)
    rwa [hr_preimage n hn a ha])
  refine ⟨d, hd, fun k hk ↦ ?_⟩
  let m := d * k
  have hm : 0 < m := Nat.mul_pos hd hk
  let N := Proj.twist 𝒜 (0 + (m : ℤ))
  let P := (pullback r).obj N
  let Q := M.tensorPow m
  let U (a : 𝒜 m) := r ⁻¹ᵁ Proj.basicOpen 𝒜 a.val
  let σ (a : 𝒜 m) := (Proj.unitToTwist a.property).app ⊤ (1 : Γ(Proj 𝒜, ⊤))
  let s (a : 𝒜 m) : Γ(P, ⊤) := pullbackSection r (σ a)
  let t (a : 𝒜 m) : Γ(Q, ⊤) := (gradedSectionElement 𝒜 M ψ a.val a.property).val m
  have hs (a : 𝒜 m) :
      IsFreeGenerator (P.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (s a)) := by
    exact isFreeGenerator_pullbackSection (g := r) (Proj.unitToTwist a.property)
  have ht (a : 𝒜 m) :
      IsFreeGenerator (Q.presheaf.map (homOfLE (le_top : U a ≤ ⊤)).op (t a)) := by
    have heq : U a = generatingLocus (t a) := by
      apply Opens.ext
      exact (hr_preimage m hm a.val a.property).trans (Set.ext fun z ↦
        mem_nonvanishingLocus_iff_generatesAt Q (t a) z)
    let F (V : Z.Opens) := IsFreeGenerator
      (Q.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t a))
    exact Eq.mpr (congrArg F heq) (isFreeGenerator_generatingLocus (t a))
  have hr (a b : 𝒜 m) : ∃ c : Γ(Z, U b),
      P.presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (s a) =
        c • P.presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (s b) ∧
      Q.presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (t a) =
        c • Q.presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (t b) := by
    have ha : a.val ∈ 𝒜 (1 • m) := by simpa only [one_nsmul] using a.property
    refine ⟨r.app (Proj.basicOpen 𝒜 b.val)
      (Proj.awayToSection 𝒜 b.val
        (HomogeneousLocalization.Away.mk 𝒜 b.property 1 a.val ha)), ?_, ?_⟩
    · exact pullbackSection_map_eq_smul r (le_top : Proj.basicOpen 𝒜 b.val ≤ ⊤)
        (Proj.map_unitToTwist_eq_smul a.property b.property ha)
    · have h := (hr_formula m hm b.val b.property 1 a.val ha).symm
      dsimp only [gradedSectionElement] at h
      simp only [pow_one] at h
      let c := r.app (Proj.basicOpen 𝒜 b.val)
        (Proj.awayToSection 𝒜 b.val
          (HomogeneousLocalization.Away.mk 𝒜 b.property 1 a.val ha))
      let F (j : ℕ) : Prop :=
        (M.tensorPow j).presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (ψ a.val j) =
          c • (M.tensorPow j).presheaf.map (homOfLE (le_top : U b ≤ ⊤)).op (ψ b.val j)
      have hF : F (1 • m) := h
      have hFm : F m := (congrArg F (show 1 • m = m from one_nsmul m)).mp hF
      exact hFm
  obtain ⟨e, he⟩ := exists_iso_of_section_ratios U (hcov k hk) s t hs ht hr
  let q := ((tensorPullbackSectionAdjunction r).leftAdjointUniq
    (pullbackPushforwardAdjunction r)).app N
  refine ⟨q ≪≫ e, fun a ha ↦ ?_⟩
  change e.hom.app (r ⁻¹ᵁ ⊤)
    (q.hom.app (r ⁻¹ᵁ ⊤) (tensorPullbackSection r N ⊤ (σ ⟨a, ha⟩))) = _
  rw [tensorPullbackSection_transport]
  simpa only [Scheme.Hom.preimage_top, presheaf_map_id_apply] using he ⟨a, ha⟩

end AlgebraicGeometry.Scheme.Modules
