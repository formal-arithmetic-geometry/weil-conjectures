/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF Q44
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.TensorObj
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# Twist comparison for a standard graded quotient

Source: Stacks Project, constructions.tex, Tags 01MY and 01N1,
lemma-morphism-proj and lemma-surjective-graded-rings-generated-degree-1-map-proj
(blueprint: lem-sfb-graded-proj-quotient-twist-comparison).

The multiplication assertion is written on local pure tensors: the product of two
sections is their pointwise product in the homogeneous prime localizations. Such
sections generate the sheaf tensor product locally, and their pulled-back sections
generate tensor pullback locally. Thus this is the full multiplication diagram.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The local section formula for the canonical multiplication of twists, in all
integer degrees. This uses the existing locally-fraction twisting sheaves and their
graded multiplication, without choosing a trivialization.
Source: Stacks Project, constructions.tex, equation-multiply and Tag 01MY
(blueprint: lem-sfb-graded-proj-quotient-twist-comparison). -/
def twistSectionProduct {A : Type u} [CommRing A]
    {𝒜 : ℕ → AddSubgroup A} [GradedRing 𝒜] {a b : ℤ} {U : (Proj 𝒜).Opens}
    (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)) : Γ(twist 𝒜 (a + b), U) :=
  ⟨fun x ↦ ⟨s.1 x * t.1 x, mul_mem_degreePart (s.1 x).2 (t.1 x).2⟩,
    ProjectiveSpectrum.Twist.isLocallyFraction_mul rfl s.2 t.2⟩

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def twistFiberMap
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) (x : Proj ℬ) (s : ProjectiveSpectrum.Twist.fiber 𝒜 n
      (ProjectiveSpectrum.comap ψ hψ x)) : ProjectiveSpectrum.Twist.fiber ℬ n x :=
  ⟨Localization.localRingHom _ _ ψ.toRingHom rfl s.1, by
    obtain h | ⟨i, j, a, b, hb, ha, hb', hij, hs⟩ := s.2
    · exact Or.inl (by rw [h, map_zero])
    · refine Or.inr ⟨i, j, ψ a, ψ b, hb, ψ.map_mem ha, ψ.map_mem hb', hij, ?_⟩
      rw [hs]
      exact Localization.localRingHom_mk _ _ _ _ _ _⟩

private theorem twistFiberMap_mk
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) (x : Proj ℬ) {i j : ℕ} (a : 𝒜 i) (b : 𝒜 j)
    (hb : (b : A) ∉ (ProjectiveSpectrum.comap ψ hψ x).asHomogeneousIdeal.toIdeal)
    (h : (i : ℤ) = j + n) :
    twistFiberMap ψ hψ n x (degreePart.mk a b hb h) =
      degreePart.mk (ψ.gradedAddHom i a) (ψ.gradedAddHom j b) hb h := by
  apply Subtype.ext
  exact Localization.localRingHom_mk _ _ _ _ _ _

private noncomputable def twistPushforwardMap
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) : twist 𝒜 n ⟶ (pushforward (map ψ hψ)).obj (twist ℬ n) := by
  refine ⟨PresheafOfModules.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ⟨fun x ↦ twistFiberMap ψ hψ n x.1 (s.1
            ⟨ProjectiveSpectrum.comap ψ hψ x.1, x.2⟩), ?_⟩
          map_zero' := ?_
          map_add' := ?_ }
      naturality := ?_ } ?_⟩
  · intro x
    obtain ⟨W, hx, e, i, j, hij, a, b, hb, hw⟩ := s.2
      ⟨ProjectiveSpectrum.comap ψ hψ x.1, x.2⟩
    refine ⟨W.comap (ProjectiveSpectrum.comap ψ hψ), hx,
      (Opens.map (map ψ hψ).base).map e, i, j, hij,
      ψ.gradedAddHom i a, ψ.gradedAddHom j b,
      fun y ↦ hb ⟨_, y.2⟩, fun y ↦ ?_⟩
    dsimp only
    change twistFiberMap ψ hψ n y.1 (s.1 (e ⟨_, y.2⟩)) = _
    exact (congrArg (twistFiberMap ψ hψ n y.1) (hw ⟨_, y.2⟩)).trans
      (twistFiberMap_mk ψ hψ n y.1 a b _ hij)
  · apply Subtype.ext
    funext x
    apply Subtype.ext
    exact map_zero _
  · intro s t
    apply Subtype.ext
    funext x
    apply Subtype.ext
    exact map_add _ _ _
  · intro U V i
    ext s
    rfl
  · intro U r s
    apply Subtype.ext
    funext x
    apply Subtype.ext
    change Localization.localRingHom _ _ ψ.toRingHom rfl
      ((r.1 ⟨_, x.2⟩).val * (s.1 ⟨_, x.2⟩).val) = _
    change Localization.localRingHom _ _ ψ.toRingHom rfl
      ((r.1 ⟨_, x.2⟩).val * (s.1 ⟨_, x.2⟩).val) =
      (HomogeneousLocalization.localRingHom ψ _ _ rfl (r.1 ⟨_, x.2⟩)).val *
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val
    rw [map_mul, val_localRingHom]
    rfl

private theorem twistPushforwardMap_val
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 n, U))
    (x : map ψ hψ ⁻¹ᵁ U) :
    (((twistPushforwardMap ψ hψ n).app U s).1 x).val =
      Localization.localRingHom _ _ ψ.toRingHom rfl
        ((s.1 ⟨ProjectiveSpectrum.comap ψ hψ x.1, x.2⟩).val) := rfl

private theorem degreeOneCover
    {A : Type u} [CommRing A] (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]
    (hgen : Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 1 : Set A)) = ⊤) :
    ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f := by
  classical
  intro x
  by_contra h
  have hp : ∀ f ∈ 𝒜 1, f ∈ x.asHomogeneousIdeal.toIdeal := by
    intro f hf
    by_contra hn
    exact h ⟨f, hf, hn⟩
  let q := Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal
  have heq : q = q.comp (GradedRing.projZeroRingHom 𝒜) := by
    apply RingHom.eq_of_eqOn_set_dense hgen
    intro a ha
    rcases ha with ha | ha
    · change q a = q (DirectSum.decompose 𝒜 a 0)
      rw [DirectSum.decompose_of_mem_same 𝒜 ha]
    · change q a = q (DirectSum.decompose 𝒜 a 0)
      rw [DirectSum.decompose_of_mem_ne 𝒜 ha (by decide : (1 : ℕ) ≠ 0), map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hp a ha)
  apply x.not_irrelevant_le
  intro a ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero : GradedRing.projZeroRingHom 𝒜 a = 0 := ha
  change q a = 0
  exact (congrArg (fun t : A →+* A ⧸ x.asHomogeneousIdeal.toIdeal ↦ t a) heq).trans
    (by change q (GradedRing.projZeroRingHom 𝒜 a) = 0; rw [hzero, map_zero])

attribute [local irreducible] tensorPullback

private noncomputable def twistPullbackMap
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) : (tensorPullback (map ψ hψ)).obj (twist 𝒜 n) ⟶ twist ℬ n :=
  ((tensorPullbackSectionAdjunction (map ψ hψ)).homEquiv _ _).symm
    (twistPushforwardMap ψ hψ n)

private theorem twistPullbackMap_section
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 n, U)) :
    (twistPullbackMap ψ hψ n).app _
      (tensorPullbackSection (map ψ hψ) (twist 𝒜 n) U s) =
        (twistPushforwardMap ψ hψ n).app U s := by
  have h := ((tensorPullbackSectionAdjunction (map ψ hψ)).homEquiv _ _).apply_symm_apply
    (twistPushforwardMap ψ hψ n)
  rw [Adjunction.homEquiv_unit] at h
  have hu := (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction
    (map ψ hψ))).1 (twist 𝒜 n) U s
  have he := congrArg (fun t ↦ t.app U s) h
  change ((pushforward (map ψ hψ)).map (twistPullbackMap ψ hψ n)).app U
    (((tensorPullbackSectionAdjunction (map ψ hψ)).unit.app (twist 𝒜 n)).app U s) = _
    at he
  change ((tensorPullbackSectionAdjunction (map ψ hψ)).unit.app
    (twist 𝒜 n)).app U s = _ at hu
  exact (congrArg ((twistPullbackMap ψ hψ n).app _) hu).symm.trans he

private theorem twistPullbackMap_frame
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (n : ℤ) (f : A) (hf : f ∈ 𝒜 1) :
    (twistPullbackMap ψ hψ n).app (basicOpen ℬ (ψ f))
      (tensorPullbackSection (map ψ hψ) (twist 𝒜 n) (basicOpen 𝒜 f)
        (twistPowSection n hf)) = twistPowSection n (ψ.map_mem hf) := by
  change (twistPullbackMap ψ hψ n).app (map ψ hψ ⁻¹ᵁ basicOpen 𝒜 f) _ = _
  rw [twistPullbackMap_section]
  apply Subtype.ext
  funext x
  apply Subtype.ext
  change Localization.localRingHom _ _ ψ.toRingHom rfl
    ((twistPowSection n hf).1 ⟨_, x.2⟩).val = _
  rw [val_twistPowSection_apply, Localization.localRingHom_mk,
    val_twistPowSection_apply]
  simp only [map_pow, GradedRingHom.coe_toRingHom]

private theorem tensorPullback_freeGenerator
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (hs : IsFreeGenerator s) :
    IsFreeGenerator (tensorPullbackSection g M U s) := by
  let adj := tensorPullbackSectionAdjunction g
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction g)).app M
  have h := (hs.pullback_unit_app g).app_hom e.symm
  have hu := adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction g) M
  have hv := congrArg (fun t ↦ t.app U s) hu
  change e.hom.app _ ((adj.unit.app M).app U s) = _ at hv
  have hn := (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction g)).1 M U s
  change (adj.unit.app M).app U s = _ at hn
  rw [hn] at hv
  have hi : e.inv.app _ (e.hom.app _ (tensorPullbackSection g M U s)) =
      tensorPullbackSection g M U s := by
    change (e.hom.app _ ≫ e.inv.app _) _ = _
    rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  have hv' := congrArg (e.inv.app (g ⁻¹ᵁ U)) hv
  have heq := hi.symm.trans hv'
  exact heq.symm ▸ h

private theorem twistPullbackMap_isIso
    {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (cover : ∀ x : Proj 𝒜, ∃ f ∈ 𝒜 1, x ∈ basicOpen 𝒜 f) (n : ℤ) :
    IsIso (twistPullbackMap ψ hψ n) := by
  apply Hom.isIso_of_forall_bijective_app
  intro x
  obtain ⟨f, hf, hx⟩ := cover ((map ψ hψ) x)
  refine ⟨basicOpen ℬ (ψ f), hx, fun W hW ↦ ?_⟩
  let s := tensorPullbackSection (map ψ hψ) (twist 𝒜 n)
    (basicOpen 𝒜 f) (twistPowSection n hf)
  have hs : IsFreeGenerator s :=
    tensorPullback_freeGenerator _ _ _ _ (isFreeGenerator_twistPowSection n hf)
  have ht := isFreeGenerator_twistPowSection n (ψ.map_mem hf)
  have he : (twistPullbackMap ψ hψ n).app W ∘
      (fun r : Γ(Proj ℬ, W) ↦ r •
        ((tensorPullback (map ψ hψ)).obj (twist 𝒜 n)).presheaf.map (homOfLE hW).op s) =
      (fun r : Γ(Proj ℬ, W) ↦ r •
        (twist ℬ n).presheaf.map (homOfLE hW).op (twistPowSection n (ψ.map_mem hf))) := by
    funext r
    rw [Function.comp_apply, Hom.app_smul, Hom.app_presheaf_map]
    exact congrArg (fun z ↦ r • (twist ℬ n).presheaf.map (homOfLE hW).op z)
      (twistPullbackMap_frame ψ hψ n f hf)
  exact (Function.Bijective.of_comp_iff _ (hs W hW)).mp (he ▸ ht W hW)

private theorem hom_ext_frames
    {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} {I : Type u}
    (U : I → X.Opens) (cover : ∀ x : X, ∃ i, x ∈ U i)
    (e : ∀ i, Γ(M, U i)) (he : ∀ i, IsFreeGenerator (e i))
    (α β : M ⟶ N) (h : ∀ i, α.app (U i) (e i) = β.app (U i) (e i)) : α = β := by
  apply hom_ext
  intro V
  ext s
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ ?_)
    (α.app V s) (β.app V s) (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := cover x
    exact Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · obtain ⟨r, hr⟩ := ((he i).map (inf_le_right : V ⊓ U i ≤ U i)).exists_smul_eq
      (M.presheaf.map (homOfLE inf_le_left).op s)
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, ← hr,
      Hom.app_smul, Hom.app_smul, Hom.app_presheaf_map, Hom.app_presheaf_map, h i]

private theorem unitToTwistZero_one_val
    {A : Type u} [CommRing A] {𝒜 : ℕ → AddSubgroup A} [GradedRing 𝒜]
    (U : (Proj 𝒜).Opens) (x : U) :
    ((Hom.app (unitToTwistZero (𝒜 := 𝒜)) U (1 : Γ(Proj 𝒜, U))).1 x).val = 1 := by
  rw [val_unitToTwistZero_app_apply, degreePart.coe_zeroEquiv_apply]
  exact HomogeneousLocalization.val_one

private theorem unitToTwist_one_val
    {A : Type u} [CommRing A] {𝒜 : ℕ → AddSubgroup A} [GradedRing 𝒜]
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (U : (Proj 𝒜).Opens) (x : U) :
    (((unitToTwist hs).app U (1 : Γ(Proj 𝒜, U))).1 x).val = Localization.mk s 1 := by
  rw [val_unitToTwist_app_apply]
  change (1 : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal).val * _ = _
  rw [HomogeneousLocalization.val_one, one_mul]

attribute [local irreducible] twistPullbackMap twistPushforwardMap

/-- The induced quotient morphism has the stated affine fraction maps and a unique
family of twist isomorphisms normalized on degree-one frames. It preserves the
unit, multiplication on every local pure tensor, and every homogeneous section.
Generation over degree zero is expressed by ring generation by the union of the
degree-zero and degree-one pieces, with no finite-generation assumption.

Source: Stacks Project, constructions.tex, Tags 01MY and 01N1
(blueprint: lem-sfb-graded-proj-quotient-twist-comparison).

Proof: Apply the graded ring map to the numerator and denominator in each prime
localization. It preserves the degree of fractions and the locally-fraction predicate,
so gives a module morphism O_P(n) → i_* O_X(n). Transpose under the section-normalized
pullback adjunction to obtain i^* O_P(n) → O_X(n). Its value on a pulled-back section
is the pointwise localization map. In particular it sends f^n to ψ(f)^n, in every
integer degree. These are free generators on the degree-one charts, and pullback
preserves free generators; thus the transposed map is locally an isomorphism.
For the covering, if a homogeneous prime contains A_1, its quotient map agrees with
its composite with the degree-zero projection on A_0 and A_1, hence on A by hgen.
It therefore contains A_+, a contradiction. Pull this cover back along i.
The localization map preserves one and products, giving the unit, multiplication,
and homogeneous-section assertions pointwise. Two comparisons satisfying the frame
condition agree on a free generator over each chart, hence everywhere by sheaf
separatedness. The chart assertions use map_preimage_basicOpen, Away.map_surjective,
Away.map_mk and awayι_comp_map. No nonzero or nonempty hypothesis is used. -/
theorem gradedQuotientTwistComparison
    {A B : Type u} [CommRing A] [CommRing B]
    (𝒜 : ℕ → AddSubgroup A) (ℬ : ℕ → AddSubgroup B) [GradedRing 𝒜] [GradedRing ℬ]
    (hgen : Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 1 : Set A)) = ⊤)
    (ψ : 𝒜 →+*ᵍ ℬ) (hψ : Function.Surjective ψ) :
    (∀ (d : ℕ) (f : A) (hf : f ∈ 𝒜 d) (hd : 0 < d),
      map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ basicOpen 𝒜 f =
        basicOpen ℬ (ψ f) ∧
      Function.Surjective (Away.map ψ f) ∧
      (∀ (r : ℕ) (a : A) (ha : a ∈ 𝒜 (r • d)),
        Away.map ψ f (Away.mk 𝒜 hf r a ha) =
          Away.mk ℬ (ψ.map_mem hf) r (ψ a) (ψ.map_mem ha)) ∧
      awayι ℬ (ψ f) (ψ.map_mem hf) hd ≫
          map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) =
        Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫ awayι 𝒜 f hf hd) ∧
    ∃! θ : ∀ n : ℤ,
        (tensorPullback (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))).obj
          (twist 𝒜 n) ≅ twist ℬ n,
      (∀ (n : ℤ) (f : A) (hf : f ∈ 𝒜 1),
        (θ n).hom.app (basicOpen ℬ (ψ f))
          (tensorPullbackSection
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
            (twist 𝒜 n) (basicOpen 𝒜 f) (twistPowSection n hf)) =
          twistPowSection n (ψ.map_mem hf)) ∧
      (∀ U : (Proj 𝒜).Opens,
        (θ 0).hom.app
          (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U)
          (tensorPullbackSection
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
            (twist 𝒜 0) U (Hom.app (unitToTwistZero (𝒜 := 𝒜)) U (1 : Γ(Proj 𝒜, U)))) =
          Hom.app (unitToTwistZero (𝒜 := ℬ))
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U)
            (1 : Γ(Proj ℬ,
              map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U))) ∧
      (∀ (a b : ℤ) (U : (Proj 𝒜).Opens)
        (s : Γ(twist 𝒜 a, U)) (t : Γ(twist 𝒜 b, U)),
        (θ (a + b)).hom.app
          (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U)
          (tensorPullbackSection
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
            (twist 𝒜 (a + b)) U (twistSectionProduct s t)) =
          twistSectionProduct
            ((θ a).hom.app
              (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U)
              (tensorPullbackSection
                (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
                (twist 𝒜 a) U s))
            ((θ b).hom.app
              (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ U)
              (tensorPullbackSection
                (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
                (twist 𝒜 b) U t))) ∧
      (∀ (d : ℕ) (s : A) (hs : s ∈ 𝒜 d),
        (θ (0 + (d : ℤ))).hom.app
          (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ ⊤)
          (tensorPullbackSection
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ))
            (twist 𝒜 (0 + (d : ℤ))) ⊤ ((unitToTwist hs).app ⊤ (1 : Γ(Proj 𝒜, ⊤)))) =
          (unitToTwist (ψ.map_mem hs)).app
            (map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ ⊤)
            (1 : Γ(Proj ℬ,
              map ψ (GradedRingHom.irrelevant_le_map_of_surjective hψ) ⁻¹ᵁ ⊤))) := by
  constructor
  · intro d f hf hd
    exact ⟨map_preimage_basicOpen ψ _ f, Away.map_surjective ψ hψ hf,
      fun r a ha ↦ Away.map_mk ψ f hf r a ha, awayι_comp_map ψ _ hd f hf⟩
  · classical
    let h := GradedRingHom.irrelevant_le_map_of_surjective hψ
    let θ (n : ℤ) := @asIso _ _ _ _ (twistPullbackMap ψ h n)
      (twistPullbackMap_isIso ψ h (degreeOneCover 𝒜 hgen) n)
    refine ⟨θ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · exact twistPullbackMap_frame ψ h
    · intro U
      change (twistPullbackMap ψ h 0).app _ _ = _
      rw [twistPullbackMap_section]
      apply Subtype.ext
      funext x
      apply Subtype.ext
      rw [twistPushforwardMap_val]
      rw [unitToTwistZero_one_val, unitToTwistZero_one_val, map_one]
    · intro a b U s t
      change (twistPullbackMap ψ h (a + b)).app _ _ =
        twistSectionProduct ((twistPullbackMap ψ h a).app _ _)
          ((twistPullbackMap ψ h b).app _ _)
      rw [twistPullbackMap_section, twistPullbackMap_section, twistPullbackMap_section]
      apply Subtype.ext
      funext x
      apply Subtype.ext
      change (((twistPushforwardMap ψ h (a + b)).app U
        (twistSectionProduct s t)).1 x).val = _
      rw [twistPushforwardMap_val]
      change Localization.localRingHom _ _ ψ.toRingHom rfl _ =
        (((twistPushforwardMap ψ h a).app U s).1 x).val *
          (((twistPushforwardMap ψ h b).app U t).1 x).val
      rw [twistPushforwardMap_val, twistPushforwardMap_val]
      exact map_mul (Localization.localRingHom _ _ ψ.toRingHom rfl) _ _
    · intro d s hs
      change (twistPullbackMap ψ h (0 + (d : ℤ))).app _ _ = _
      rw [twistPullbackMap_section]
      apply Subtype.ext
      funext x
      apply Subtype.ext
      rw [twistPushforwardMap_val]
      rw [unitToTwist_one_val, unitToTwist_one_val]
      rw [Localization.localRingHom_mk]
      congr 1
      exact Subtype.ext (map_one ψ.toRingHom)
    · intro τ hτ
      funext n
      apply Iso.ext
      let U (i : {f : A // f ∈ 𝒜 1}) := basicOpen ℬ (ψ i.1)
      let e (i : {f : A // f ∈ 𝒜 1}) :=
        tensorPullbackSection (map ψ h) (twist 𝒜 n) (basicOpen 𝒜 i.1)
          (twistPowSection n i.2)
      apply hom_ext_frames U (fun x ↦ ?_) e (fun i ↦ ?_) (τ n).hom (θ n).hom
      · intro i
        exact (hτ.1 n i.1 i.2).trans (twistPullbackMap_frame ψ h n i.1 i.2).symm
      · obtain ⟨f, hf, hx⟩ := degreeOneCover 𝒜 hgen ((map ψ h) x)
        exact ⟨⟨f, hf⟩, hx⟩
      · exact tensorPullback_freeGenerator _ _ _ _ (isFreeGenerator_twistPowSection n i.2)

end AlgebraicGeometry.Proj
