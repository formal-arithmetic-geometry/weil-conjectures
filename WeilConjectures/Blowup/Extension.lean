/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion

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

Third, the canonical lift along a blow-up localizes on the base: over an open of the
base on which two centres agree, their canonical lifts agree, so an open-immersion
statement for one of them transfers to the other (Stacks Project Tag 0806, local form).

Fourth, a finite-type centre on a quasi-compact open extends to the whole scheme
keeping its support away from a second quasi-compact open which it already avoids
(Stacks Project Tag 080M). Unlike `AlgebraicGeometry.IsAdmissible.exists_extend` this
needs no containment between the two opens.

Fifth, the product of two `U`-admissible centers is `U`-admissible
(bookkeeping for blueprint `lemma:nagata-product-ideal-common-blowup`).

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.exists_isPullback_blowup_comap` — the
  blow-up of the restriction of an ideal along an open immersion is the restriction of the
  blow-up (blueprint: `thm:nagata-blowup-flat-base-change`, open-immersion case), and its
  corollary `AlgebraicGeometry.Scheme.IdealSheafData.exists_blowup_comap_iso` for
  isomorphisms;
- `AlgebraicGeometry.IsAdmissible.exists_extend` — extension of admissible centers
  across a quasi-compact open (blueprint: `def:nagata-extended-admissible-blowup`,
  `lemma:nagata-extend-admissible-blowup`);
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens` — the
  canonical lift localizes on the base (Stacks Project Tag 0806, local form);
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_comap_eq_of_disjoint` —
  gluing a finite-type centre across two overlapping quasi-compact opens (Stacks Project
  Tag 080M);
- `AlgebraicGeometry.IsAdmissible.mul` — the product of two admissible centers
  (blueprint: `lemma:nagata-product-ideal-common-blowup`, bookkeeping).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Blow-ups restrict along open immersions** (the open-immersion case of the blow-up
flat base change theorem, blueprint `thm:nagata-blowup-flat-base-change`): the blow-up of
the restriction `I.comap q` of an ideal sheaf `I` along an open immersion `q : Y ⟶ X` fits
into a cartesian square over the blow-up of `I`, via the canonical lift of
`(I.comap q).blowupMap ≫ q` through the universal property of `I.blowup`. -/
theorem Scheme.IdealSheafData.exists_isPullback_blowup_comap
    {X Y : Scheme.{u}} (I : X.IdealSheafData) (q : Y ⟶ X) [IsOpenImmersion q] :
    ∃ h : (I.comap q).blowup ⟶ I.blowup,
      h ≫ I.blowupMap = (I.comap q).blowupMap ≫ q ∧
      IsPullback (I.comap q).blowupMap h q I.blowupMap := by
  -- the composite to `X` pulls `I` back to an invertible ideal, hence lifts
  obtain ⟨h, hh⟩ := I.exists_lift_blowup (t := (I.comap q).blowupMap ≫ q) (by
    rw [Scheme.IdealSheafData.comap_comp]
    exact (I.comap q).isInvertible_comap_blowupMap)
  -- the first projection of the pullback lifts through the blow-up of `I.comap q`
  obtain ⟨k, hk⟩ := (I.comap q).exists_lift_blowup
    (t := pullback.fst q I.blowupMap) (by
      rw [← Scheme.IdealSheafData.comap_comp, pullback.condition,
        Scheme.IdealSheafData.comap_comp]
      exact I.isInvertible_comap_blowupMap.comap_of_isOpenImmersion _)
  refine ⟨h, hh, IsPullback.of_iso_pullback ⟨hh.symm⟩
    ⟨pullback.lift (I.comap q).blowupMap h hh.symm, k, ?_, ?_⟩
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
  · -- `lift ≫ k = 𝟙`: both sides are lifts of the blow-up map of `I.comap q`
    refine (I.comap q).hom_ext_of_isInvertible_comap
      (I.comap q).isInvertible_comap_blowupMap ?_ (Category.id_comp _)
    rw [Category.assoc, hk, pullback.lift_fst]
  · -- `k ≫ lift = 𝟙`: compare both projections out of the pullback
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, hk, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      -- `k ≫ h = pullback.snd`: both sides are lifts of `pullback.snd ≫ I.blowupMap`
      refine I.hom_ext_of_isInvertible_comap
        (t := pullback.snd q I.blowupMap ≫ I.blowupMap) ?_ ?_ rfl
      · rw [Scheme.IdealSheafData.comap_comp]
        exact I.isInvertible_comap_blowupMap.comap_of_isOpenImmersion _
      · rw [Category.assoc, hh, ← Category.assoc, hk, pullback.condition]

/-- **Blow-ups are invariant under isomorphisms of the base**: for an isomorphism
`e : Y ≅ X` and an ideal sheaf `I` on `X`, the blow-up of `I.comap e.hom` is the blow-up
of `I`, compatibly with the structure morphisms. -/
theorem Scheme.IdealSheafData.exists_blowup_comap_iso {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (e : Y ≅ X) :
    ∃ f : (I.comap e.hom).blowup ≅ I.blowup,
      f.hom ≫ I.blowupMap = (I.comap e.hom).blowupMap ≫ e.hom := by
  obtain ⟨h, hh, hpb⟩ := I.exists_isPullback_blowup_comap e.hom
  have : IsIso h := hpb.isIso_snd_of_isIso
  exact ⟨asIso h, hh⟩

/-- **The canonical lift of a blow-up localizes on the base** (the local form of Stacks
Project Tag 0806): let `I` be an ideal sheaf on `X`, `f : Y ⟶ X` a morphism and
`l : Bl_{I·O_Y}(Y) ⟶ Bl_I(X)` the canonical lift of `f`. For an open `O ⊆ X` on which
`I` restricts to `JO`, the corresponding lift `μ` for `JO` and the restriction of `f`
over `O` fits into a commuting square with `l` whose horizontal legs are the open
immersions cutting out the loci over `O`. In particular the two lifts agree over `O`:
the square identifies `l` above `O` with `μ`.

Both horizontal legs come from the restriction theorem for blow-ups along open
immersions (`Scheme.IdealSheafData.exists_isPullback_blowup_comap`), and the square
commutes by uniqueness of lifts
(`Scheme.IdealSheafData.hom_ext_of_isInvertible_comap`). -/
theorem Scheme.IdealSheafData.exists_comm_lift_blowup_comap_opens {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (f : Y ⟶ X) (O : X.Opens)
    {JO : O.toScheme.IdealSheafData} (hJO : I.comap O.ι = JO)
    {l : (I.comap f).blowup ⟶ I.blowup}
    (hl : l ≫ I.blowupMap = (I.comap f).blowupMap ≫ f)
    {μ : (JO.comap (f ∣_ O)).blowup ⟶ JO.blowup}
    (hμ : μ ≫ JO.blowupMap = (JO.comap (f ∣_ O)).blowupMap ≫ (f ∣_ O)) :
    ∃ (h : JO.blowup ⟶ I.blowup) (h' : (JO.comap (f ∣_ O)).blowup ⟶ (I.comap f).blowup),
      IsOpenImmersion h ∧ IsOpenImmersion h' ∧ h' ≫ l = μ ≫ h ∧
      Set.range h = I.blowupMap ⁻¹' (O : Set X) ∧
      Set.range h' = (l ≫ I.blowupMap) ⁻¹' (O : Set X) := by
  subst hJO
  have hfO : (f ∣_ O) ≫ O.ι = (f ⁻¹ᵁ O).ι ≫ f := morphismRestrict_ι f O
  have hcomap : (I.comap O.ι).comap (f ∣_ O) = (I.comap f).comap (f ⁻¹ᵁ O).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hfO, Scheme.IdealSheafData.comap_comp]
  -- the locus over `O` in the blow-up of `I`
  obtain ⟨h, hh, hpb⟩ := I.exists_isPullback_blowup_comap O.ι
  haveI : IsOpenImmersion h := IsOpenImmersion.of_isPullback hpb inferInstance
  -- the locus over `f ⁻¹ᵁ O` in the blow-up of `I.comap f`
  obtain ⟨h₀, hh₀, hpb₀⟩ := (I.comap f).exists_isPullback_blowup_comap (f ⁻¹ᵁ O).ι
  haveI : IsOpenImmersion h₀ := IsOpenImmersion.of_isPullback hpb₀ inferInstance
  obtain ⟨h', hOI', hh'blow, hh'range⟩ :
      ∃ h' : ((I.comap O.ι).comap (f ∣_ O)).blowup ⟶ (I.comap f).blowup,
        IsOpenImmersion h' ∧
        h' ≫ (I.comap f).blowupMap =
          ((I.comap O.ι).comap (f ∣_ O)).blowupMap ≫ (f ⁻¹ᵁ O).ι ∧
        Set.range h' = Set.range h₀ := by
    have hsurj : Function.Surjective
        ⇑(eqToHom (congrArg Scheme.IdealSheafData.blowup hcomap) :
          ((I.comap O.ι).comap (f ∣_ O)).blowup ⟶
            ((I.comap f).comap (f ⁻¹ᵁ O).ι).blowup) := by
      have := (Scheme.homeoOfIso (asIso
        (eqToHom (congrArg Scheme.IdealSheafData.blowup hcomap) :
          ((I.comap O.ι).comap (f ∣_ O)).blowup ⟶
            ((I.comap f).comap (f ⁻¹ᵁ O).ι).blowup))).surjective
      rwa [Scheme.coe_homeoOfIso] at this
    refine ⟨eqToHom (congrArg Scheme.IdealSheafData.blowup hcomap) ≫ h₀, inferInstance,
      ?_, ?_⟩
    · rw [Category.assoc, hh₀, ← Category.assoc,
        Scheme.IdealSheafData.eqToHom_comp_blowupMap hcomap]
    · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr hsurj, Set.image_univ]
  haveI := hOI'
  refine ⟨h, h', inferInstance, inferInstance, ?_, ?_, ?_⟩
  · -- the square commutes, by uniqueness of lifts along `I.blowupMap`
    refine I.hom_ext_of_isInvertible_comap
      (t := h' ≫ (I.comap f).blowupMap ≫ f) ?_ ?_ ?_
    · simp only [Scheme.IdealSheafData.comap_comp]
      exact ((I.comap f).isInvertible_comap_blowupMap).comap_of_isOpenImmersion h'
    · rw [Category.assoc, hl]
    · rw [Category.assoc, hh, ← Category.assoc, hμ, Category.assoc, hfO,
        ← Category.assoc, ← hh'blow, Category.assoc]
  · -- the range of the first leg
    rw [range_snd_of_isPullback hpb, Scheme.Opens.range_ι]
  · -- the range of the second leg
    rw [hh'range, range_snd_of_isPullback hpb₀, Scheme.Opens.range_ι, hl,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    rfl

/-- **Gluing a finite-type centre across two overlapping quasi-compact opens** (Stacks
Project Tag 080M): let `A`, `B` be quasi-compact opens of a quasi-compact
quasi-separated scheme `X` and let `J` be a finite-type ideal sheaf on `A` whose
support avoids `B`. Then `J` extends to a finite-type ideal sheaf on `X` whose support
still avoids `B`.

Unlike `AlgebraicGeometry.IsAdmissible.exists_extend`, no containment between `A` and
`B` is assumed; this is what makes the extension usable when the open to be avoided is
not contained in the open carrying the centre. The extension is built in two steps:
the naive extension `J.map A.ι` already avoids `B`, because `B` is open and misses the
image of the support of `J`, and it is of finite type on `A ⊔ B` (equal to `J` on `A`
and to the unit ideal on `B`); the finite-type extension theorem (Stacks Project
Tag 01PF) then produces a finite-type ideal sheaf on all of `X` with the same
restriction to `A ⊔ B`. -/
theorem Scheme.IdealSheafData.exists_finiteType_comap_eq_of_disjoint {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {A B : X.Opens} (hA : IsCompact (A : Set X))
    (hB : IsCompact (B : Set X)) (J : A.toScheme.IdealSheafData) (hJ : J.ofFiniteType)
    (hdisj : Disjoint ((A.ι ⁻¹ᵁ B : A.toScheme.Opens) : Set A.toScheme)
      (J.support : Set A.toScheme)) :
    ∃ K : X.IdealSheafData, K.ofFiniteType ∧ K.comap A.ι = J ∧
      Disjoint (B : Set X) (K.support : Set X) := by
  haveI : CompactSpace A.toScheme := isCompact_iff_compactSpace.mp hA
  -- the naive extension by zero
  set G : X.IdealSheafData := J.map A.ι with hGdef
  have hGA : G.comap A.ι = J := Scheme.IdealSheafData.comap_map A.ι J
  -- it avoids `B`: `B` is open, so it meets the closure of `A.ι '' supp J` only if it
  -- meets `A.ι '' supp J` itself
  have hGB : Disjoint (B : Set X) (G.support : Set X) := by
    rw [Set.disjoint_left]
    intro x hxB hxG
    rw [hGdef, Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure]
      at hxG
    obtain ⟨z, hzB, y, hyJ, rfl⟩ := mem_closure_iff.mp hxG B B.isOpen hxB
    exact Set.disjoint_left.mp hdisj (show y ∈ (A.ι ⁻¹ᵁ B : A.toScheme.Opens) from hzB) hyJ
  -- it is the unit ideal on `B`
  have hGtopB : G.comap B.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext1
    rw [Scheme.IdealSheafData.coe_support_comap, TopologicalSpace.Closeds.coe_bot]
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦ ?_
    have hyB : B.ι y ∈ (B : Set X) := by
      have : B.ι y ∈ Set.range B.ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    exact Set.disjoint_left.mp hGB hyB hy
  -- hence of finite type on `A ⊔ B`
  have hft : G.ofFiniteTypeOn (A ⊔ B) := by
    refine Scheme.IdealSheafData.ofFiniteTypeOn.sup ?_ ?_
    · rw [Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap, hGA]
      exact hJ
    · rw [Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap, hGtopB]
      intro U _
      have htop : ((⊤ : B.toScheme.IdealSheafData).ideal U) = ⊤ := rfl
      rw [htop]
      exact ⟨{1}, by simp⟩
  -- extend from `A ⊔ B` to `X` (Stacks Tag 01PF)
  have hABcpt : IsCompact ((A ⊔ B : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_sup]
    exact hA.union hB
  obtain ⟨K, -, hKft, hKcomap⟩ :=
    Scheme.IdealSheafData.exists_finiteType_le_comap_eq G (A ⊔ B) hABcpt hft
  have hres : ∀ H : X.IdealSheafData,
      H.comap A.ι = (H.comap (A ⊔ B).ι).comap (X.homOfLE (le_sup_left : A ≤ A ⊔ B)) := by
    intro H
    rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
  refine ⟨K, hKft, ?_, ?_⟩
  · rw [hres K, hKcomap, ← hres G, hGA]
  · rw [Set.disjoint_left]
    intro x hxB hxK
    obtain ⟨y, rfl⟩ : x ∈ Set.range (A ⊔ B).ι := by
      rw [Scheme.Opens.range_ι]
      exact (le_sup_right : B ≤ A ⊔ B) hxB
    have hy : y ∈ (((K.comap (A ⊔ B).ι).support) : Set (A ⊔ B).toScheme) := by
      rw [Scheme.IdealSheafData.coe_support_comap]
      exact hxK
    rw [hKcomap, Scheme.IdealSheafData.coe_support_comap] at hy
    exact Set.disjoint_left.mp hGB hxB hy

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
  obtain ⟨h, hh, hpb⟩ := (I₁ * I₀).exists_isPullback_blowup_comap W.ι
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
