/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup

/-!

# Open restriction and extension of blow-ups

Four pieces of infrastructure for the common-modification theorem (Stacks Project
Tag 0F3X) and for the isomorphism-near-the-boundary theorem (Stacks Project Tag 0F3W).

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

Third, the canonical lift `Bl_{I·𝒪_Y}(Y) ⟶ Bl_I(X)` of a morphism `f : Y ⟶ X` through
the universal property of blowing up localizes on the base: over the locus above an
open `O ≤ X` it is the canonical lift attached to the restricted center `I.comap O.ι`
and the restricted morphism `f ∣_ O`. In particular two centers agreeing over `O` have
isomorphic lifts over `O`.

Fourth, the product of two `U`-admissible centers is `U`-admissible
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
- `AlgebraicGeometry.Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup`
  — the canonical lift of a blow-up localizes on the base, and its consequence
  `AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_morphismRestrict_lift_blowup_congr`
  for two centers agreeing over an open;
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

/-- **The canonical lift of a blow-up localizes on the base**: for `f : Y ⟶ X`, an
ideal `D` on `X` and an open `O ≤ X`, the canonical lift `l : Bl_{D·𝒪_Y}(Y) ⟶ Bl_D(X)`
restricted over the locus `D.blowupMap ⁻¹ᵁ O` above `O` is, as an arrow, the canonical
lift for the restricted center `D.comap O.ι` and the restricted morphism `f ∣_ O`.

The ideals `E` and `F` are the restrictions of `D` to `O` and of `D.comap f` to
`f ⁻¹ᵁ O`; they are taken as parameters, so that two centers agreeing over `O` can be
compared through the *same* restricted lift `m` (see
`Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup_of_comap_eq`).

Both cartesian squares come from `Scheme.IdealSheafData.exists_isPullback_blowup_comap`
(for `O.ι` on `X` and for `(f ⁻¹ᵁ O).ι` on `Y`); pasting them with the cartesian square
of `f ∣_ O` exhibits `m` as a base change of `l` along `O.ι`, and the identification of
the two squares is uniqueness of lifts
(`Scheme.IdealSheafData.hom_ext_comap_blowup`, Stacks Project Tag 0806). -/
theorem Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup
    {X Y : Scheme.{u}} {D : X.IdealSheafData} {f : Y ⟶ X} {O : X.Opens}
    {E : O.toScheme.IdealSheafData} (hE : D.comap O.ι = E)
    {F : (f ⁻¹ᵁ O).toScheme.IdealSheafData} (hF : (D.comap f).comap (f ⁻¹ᵁ O).ι = F)
    {l : (D.comap f).blowup ⟶ D.blowup}
    (hl : l ≫ D.blowupMap = (D.comap f).blowupMap ≫ f)
    {m : F.blowup ⟶ E.blowup}
    (hm : m ≫ E.blowupMap = F.blowupMap ≫ (f ∣_ O)) :
    Nonempty (Arrow.mk (l ∣_ (D.blowupMap ⁻¹ᵁ O)) ≅ Arrow.mk m) := by
  subst hE
  subst hF
  -- the two open-restriction squares of the blow-up
  obtain ⟨h, hh, hhpb⟩ := D.exists_isPullback_blowup_comap O.ι
  obtain ⟨k, hk, hkpb⟩ := (D.comap f).exists_isPullback_blowup_comap (f ⁻¹ᵁ O).ι
  -- the square `k, m, l, h` commutes, both composites being lifts along `D.blowupMap`
  have hcomm : k ≫ l = m ≫ h := by
    refine D.hom_ext_of_isInvertible_comap
      (t := ((D.comap f).comap (f ⁻¹ᵁ O).ι).blowupMap ≫ (f ⁻¹ᵁ O).ι ≫ f) ?_ ?_ ?_
    · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
      exact ((D.comap f).comap (f ⁻¹ᵁ O).ι).isInvertible_comap_blowupMap
    · rw [Category.assoc, hl, ← Category.assoc, hk, Category.assoc]
    · rw [Category.assoc, hh, ← Category.assoc, hm, Category.assoc, morphismRestrict_ι]
  -- and it is cartesian: paste the two squares below it and cancel the bottom one
  have hsq : IsPullback k m l h := by
    refine IsPullback.of_bot ?_ hcomm hhpb.flip
    rw [hm, hl]
    exact hkpb.flip.paste_vert (isPullback_morphismRestrict f O).flip
  -- the blow-up of the restricted center is the locus above `O`
  let φ : (D.comap O.ι).blowup ≅ (D.blowupMap ⁻¹ᵁ O).toScheme :=
    hhpb.flip.isoIsPullback _ _ (isPullback_morphismRestrict D.blowupMap O).flip
  have hφ : φ.hom ≫ (D.blowupMap ⁻¹ᵁ O).ι = h :=
    hhpb.flip.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict D.blowupMap O).flip
  -- hence `m` and the restriction of `l` are two base changes of `l` along the same
  -- open immersion
  have hsq' : IsPullback (m ≫ φ.hom) k (D.blowupMap ⁻¹ᵁ O).ι l := by
    have := hsq.flip.paste_horiz
      (IsPullback.of_horiz_isIso (P := (D.comap O.ι).blowup) ⟨by rw [hφ, Category.comp_id]⟩)
    simpa using this
  let ψ : ((D.comap f).comap (f ⁻¹ᵁ O).ι).blowup ≅
      (l ⁻¹ᵁ (D.blowupMap ⁻¹ᵁ O)).toScheme :=
    hsq'.isoIsPullback _ _ (isPullback_morphismRestrict l (D.blowupMap ⁻¹ᵁ O))
  have hψ : ψ.hom ≫ (l ∣_ (D.blowupMap ⁻¹ᵁ O)) = m ≫ φ.hom :=
    hsq'.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict l (D.blowupMap ⁻¹ᵁ O))
  have hw : ψ.inv ≫ m = (l ∣_ (D.blowupMap ⁻¹ᵁ O)) ≫ φ.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hψ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact ⟨Arrow.isoMk ψ.symm φ.symm hw⟩

/-- **Two centers agreeing over an open have the same canonical lift over that open**:
if `D₁` and `D₂` restrict to the same ideal on an open `O ≤ X`, then the canonical
lifts `lᵢ : Bl_{Dᵢ·𝒪_Y}(Y) ⟶ Bl_{Dᵢ}(X)` of a morphism `f : Y ⟶ X`, restricted over
the loci `Dᵢ.blowupMap ⁻¹ᵁ O` above `O`, are isomorphic as arrows.

Both are identified with the canonical lift of `f ∣_ O` for the common restricted
center, by
`Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup`. -/
theorem Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup_of_comap_eq
    {X Y : Scheme.{u}} {O : X.Opens} {D₁ D₂ : X.IdealSheafData}
    (hD : D₁.comap O.ι = D₂.comap O.ι) {f : Y ⟶ X}
    {l₁ : (D₁.comap f).blowup ⟶ D₁.blowup}
    (hl₁ : l₁ ≫ D₁.blowupMap = (D₁.comap f).blowupMap ≫ f)
    {l₂ : (D₂.comap f).blowup ⟶ D₂.blowup}
    (hl₂ : l₂ ≫ D₂.blowupMap = (D₂.comap f).blowupMap ≫ f) :
    Nonempty (Arrow.mk (l₁ ∣_ (D₁.blowupMap ⁻¹ᵁ O)) ≅
      Arrow.mk (l₂ ∣_ (D₂.blowupMap ⁻¹ᵁ O))) := by
  -- restricting to `f ⁻¹ᵁ O` is restricting to `O` and then base changing along `f ∣_ O`
  have hEF : (D₁.comap O.ι).comap (f ∣_ O) = (D₁.comap f).comap (f ⁻¹ᵁ O).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have hF : (D₂.comap f).comap (f ⁻¹ᵁ O).ι = (D₁.comap f).comap (f ⁻¹ᵁ O).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      ← morphismRestrict_ι f O, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, hD]
  -- the canonical lift of `f ∣_ O` for the common restricted center
  obtain ⟨m, hm⟩ := (D₁.comap O.ι).exists_lift_blowup
    (t := ((D₁.comap f).comap (f ⁻¹ᵁ O).ι).blowupMap ≫ (f ∣_ O))
    (by rw [Scheme.IdealSheafData.comap_comp, hEF]
        exact ((D₁.comap f).comap (f ⁻¹ᵁ O).ι).isInvertible_comap_blowupMap)
  obtain ⟨e₁⟩ :=
    Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup rfl rfl hl₁ hm
  obtain ⟨e₂⟩ :=
    Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup hD.symm hF hl₂ hm
  exact ⟨e₁ ≪≫ e₂.symm⟩

/-- **Being an open immersion over an open of the base only depends on the center
there**: if `D₁` and `D₂` restrict to the same ideal on an open `O ≤ X`, then the
canonical lift of `f : Y ⟶ X` to the blow-up of `D₁` is an open immersion over `O`
exactly when the canonical lift to the blow-up of `D₂` is. -/
theorem Scheme.IdealSheafData.isOpenImmersion_morphismRestrict_lift_blowup_congr
    {X Y : Scheme.{u}} {O : X.Opens} {D₁ D₂ : X.IdealSheafData}
    (hD : D₁.comap O.ι = D₂.comap O.ι) {f : Y ⟶ X}
    {l₁ : (D₁.comap f).blowup ⟶ D₁.blowup}
    (hl₁ : l₁ ≫ D₁.blowupMap = (D₁.comap f).blowupMap ≫ f)
    {l₂ : (D₂.comap f).blowup ⟶ D₂.blowup}
    (hl₂ : l₂ ≫ D₂.blowupMap = (D₂.comap f).blowupMap ≫ f) :
    IsOpenImmersion (l₁ ∣_ (D₁.blowupMap ⁻¹ᵁ O)) ↔
      IsOpenImmersion (l₂ ∣_ (D₂.blowupMap ⁻¹ᵁ O)) := by
  obtain ⟨e⟩ :=
    Scheme.IdealSheafData.nonempty_arrowIso_morphismRestrict_lift_blowup_of_comap_eq
      hD hl₁ hl₂
  exact MorphismProperty.arrow_mk_iso_iff (P := @IsOpenImmersion) e

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
