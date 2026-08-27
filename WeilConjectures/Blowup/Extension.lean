/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup

/-!

# Open restriction and extension of blow-ups

Three pieces of infrastructure for the common-modification theorem (Stacks Project
Tag 0F3X).

First, blow-up formation commutes with restriction to an open subscheme: the blow-up
of the restricted ideal is the pullback of the blow-up along the open immersion. This
is the open-immersion case of the blow-up flat base change theorem
(blueprint: `thm:nagata-blowup-flat-base-change`).

Second, a finite-type center on a quasi-compact open `W` of a quasi-compact
quasi-separated scheme, admissible with respect to an open `U ≤ W`, extends to a
`U`-admissible center on the ambient scheme whose blow-up restricts over `W` to the
blow-up of the original center: extend the ideal by finite-type extension (Stacks
Project Tag 01PF) and multiply by a finite-type ideal cutting out the boundary of `W`
(Stacks Project Tag 01PH), in the style of Stacks Project Tag 080M
(blueprint: `def:nagata-extended-admissible-blowup`,
`lemma:nagata-extend-admissible-blowup`).

Third, the product of two `U`-admissible centers is `U`-admissible
(bookkeeping for blueprint `lemma:nagata-product-ideal-common-blowup`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.exists_isPullback_blowup_comap` — the
  blow-up of the restriction of an ideal to an open is the restriction of the blow-up
  (blueprint: `thm:nagata-blowup-flat-base-change`, open-immersion case);
- `AlgebraicGeometry.IsAdmissible.exists_extend` — extension of admissible centers
  across a quasi-compact open (blueprint: `def:nagata-extended-admissible-blowup`,
  `lemma:nagata-extend-admissible-blowup`);
- `AlgebraicGeometry.IsAdmissible.mul` — the product of two admissible centers
  (blueprint: `lemma:nagata-product-ideal-common-blowup`, bookkeeping).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Blow-ups restrict to opens** (the open-immersion case of the blow-up flat base
change theorem, blueprint `thm:nagata-blowup-flat-base-change`): the blow-up of the
restriction `I.comap W.ι` of an ideal sheaf `I` to an open `W` fits into a cartesian
square over the blow-up of `I`, via the canonical lift of
`(I.comap W.ι).blowupMap ≫ W.ι` through the universal property of `I.blowup`. -/
theorem Scheme.IdealSheafData.exists_isPullback_blowup_comap
    {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.Opens) :
    ∃ h : (I.comap W.ι).blowup ⟶ I.blowup,
      h ≫ I.blowupMap = (I.comap W.ι).blowupMap ≫ W.ι ∧
      IsPullback (I.comap W.ι).blowupMap h W.ι I.blowupMap := by
  -- the composite to `X` pulls `I` back to an invertible ideal, hence lifts
  obtain ⟨h, hh⟩ := I.exists_lift_blowup (t := (I.comap W.ι).blowupMap ≫ W.ι) (by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (I.comap W.ι).isInvertible_comap_blowupMap)
  -- the first projection of the pullback lifts through the blow-up of `I.comap W.ι`
  obtain ⟨k, hk⟩ := (I.comap W.ι).exists_lift_blowup
    (t := pullback.fst W.ι I.blowupMap) (by
      rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
        Scheme.IdealSheafData.comap_comp]
      exact I.isInvertible_comap_blowupMap.comap_of_isOpenImmersion _)
  refine ⟨h, hh, IsPullback.of_iso_pullback ⟨hh.symm⟩
    ⟨pullback.lift (I.comap W.ι).blowupMap h hh.symm, k, ?_, ?_⟩
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
  · -- `lift ≫ k = 𝟙`: both sides are lifts of the blow-up map of `I.comap W.ι`
    refine (I.comap W.ι).hom_ext_of_isInvertible_comap
      (I.comap W.ι).isInvertible_comap_blowupMap ?_ (Category.id_comp _)
    rw [Category.assoc, hk, pullback.lift_fst]
  · -- `k ≫ lift = 𝟙`: compare both projections out of the pullback
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hk, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      -- `k ≫ h = pullback.snd`: both sides are lifts of `pullback.snd ≫ I.blowupMap`
      refine I.hom_ext_of_isInvertible_comap
        (t := pullback.snd W.ι I.blowupMap ≫ I.blowupMap) ?_ ?_ rfl
      · rw [Scheme.IdealSheafData.comap_comp]
        exact I.isInvertible_comap_blowupMap.comap_of_isOpenImmersion _
      · rw [Category.assoc, hh, ← Category.assoc, hk, pullback.condition]

/-- **Extension of admissible blow-up centers across a quasi-compact open** (in the
style of Stacks Project Tag 080M; blueprint `def:nagata-extended-admissible-blowup`,
`lemma:nagata-extend-admissible-blowup`): a finite-type center `J` on a quasi-compact
open `W` of a quasi-compact quasi-separated scheme `X`, whose support is disjoint from
an open `U ≤ W`, extends to a `U`-admissible center on `X` whose blow-up restricts
over `W` to the blow-up of `J`. The extended center is the product of a finite-type
extension of `J` (Stacks Project Tag 01PF) with a finite-type ideal cutting out the
boundary of `W` (Stacks Project Tag 01PH). -/
theorem IsAdmissible.exists_extend {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {W : X.Opens} (hW : IsCompact (W : Set X)) {U : X.Opens}
    (hUW : U ≤ W) (J : W.toScheme.IdealSheafData) (hJ : J.ofFiniteType)
    (hdisj : Disjoint ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme)
      (J.support : Set W.toScheme)) :
    ∃ (B : IsAdmissible X U) (h : J.blowup ⟶ B.I.blowup),
      h ≫ B.I.blowupMap = J.blowupMap ≫ W.ι ∧
      IsPullback J.blowupMap h W.ι B.I.blowupMap := by
  -- extend `J` to a finite-type ideal `I₁` on `X` (Stacks Tag 01PF)
  obtain ⟨I₁, hI₁ft, hI₁comap⟩ :=
    Scheme.IdealSheafData.exists_finiteType_comap_eq W hW J hJ
  -- a finite-type ideal `I₀` cutting out the boundary of `W` (Stacks Tag 01PH)
  obtain ⟨I₀, hI₀ft, hI₀supp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl W hW
  -- the support of `I₁` is disjoint from `U`, since its trace on `W` is `supp J`
  have hdisj₁ : Disjoint (U : Set X) (I₁.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxU hxI
    obtain ⟨y, rfl⟩ : x ∈ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      exact hUW hxU
    refine Set.disjoint_left.mp hdisj
      (show y ∈ (W.ι ⁻¹ᵁ U : W.toScheme.Opens) from hxU) ?_
    have hJsupp := Scheme.IdealSheafData.coe_support_comap I₁ W.ι
    rw [hI₁comap] at hJsupp
    rw [hJsupp]
    exact hxI
  -- the support of `I₀` is the complement of `W ⊇ U`, hence disjoint from `U`
  have hdisj₀ : Disjoint (U : Set X) (I₀.support : Set X) := by
    rw [hI₀supp]
    exact Set.disjoint_left.mpr fun x hxU hxW ↦ hxW (hUW hxU)
  -- admissibility of the product center `I₁ * I₀`
  have hdisjK : Disjoint (U : Set X) (((I₁ * I₀).support : Set X)) := by
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    exact Set.disjoint_union_right.mpr ⟨hdisj₁, hdisj₀⟩
  -- `I₀` restricts to the unit ideal on `W`, so `I₁ * I₀` restricts to `J`
  have hcomap : (I₁ * I₀).comap W.ι = J := by
    have htop : I₀.comap W.ι = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      ext1
      rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        hI₀supp]
      ext x
      simp
    rw [Scheme.IdealSheafData.comap_mul, hI₁comap, htop,
      Scheme.IdealSheafData.mul_top]
  -- the restriction theorem for the product center concludes
  obtain rfl := hcomap
  obtain ⟨h, hh, hpb⟩ := (I₁ * I₀).exists_isPullback_blowup_comap W
  exact ⟨⟨I₁ * I₀, hI₁ft.mul hI₀ft, hdisjK⟩, h, hh, hpb⟩

/-- **The product of two `U`-admissible centers is `U`-admissible** (bookkeeping for
blueprint `lemma:nagata-product-ideal-common-blowup`): finite-typeness is stable under
products, and the support of a product is the union of the supports. -/
def IsAdmissible.mul {X : Scheme.{u}} {U : X.Opens} (B₁ B₂ : IsAdmissible X U) :
    IsAdmissible X U where
  I := B₁.I * B₂.I
  finiteType := B₁.finiteType.mul B₂.finiteType
  disjoint_support := by
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    exact Set.disjoint_union_right.mpr ⟨B₁.disjoint_support, B₂.disjoint_support⟩

/-- The center of the product of two admissible centers is the product of the
centers. -/
@[simp]
lemma IsAdmissible.I_mul {X : Scheme.{u}} {U : X.Opens} (B₁ B₂ : IsAdmissible X U) :
    (B₁.mul B₂).I = B₁.I * B₂.I :=
  rfl

end AlgebraicGeometry
