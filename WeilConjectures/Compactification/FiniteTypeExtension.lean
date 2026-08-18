/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic

/-!

# Finite-type extension of ideals: the affine algebra layer

This file begins Phase A of the formalization plan
`blueprint/src/version/detailed/nagata/nagata_new_proof_order.md` for the Stacks
Project tags 01PF (finite-type extension of quasi-coherent submodules) and 01PH
(quasi-compact opens are complements of finite-type vanishing loci), which are the
remaining leaves of `WeilConjectures.Blowup.Admissible`.

The purely ring-theoretic inputs are proved in the mirror tree: the affine
finite-generation core of Tag 01PF (blueprint §1.2.B),
`Ideal.exists_fg_le_map_localization_eq` in
`WeilConjectures.Mathlib.RingTheory.Localization.Away.Basic`; the compactness
micro-lemma of blueprint §2.4, `Ideal.FG.isCompact_compl_zeroLocus` in
`WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology`; and retrocompactness
(blueprint §2.2), `Scheme.Opens.quasiCompact_ι` in
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.

## Main results

- `Scheme.IdealSheafData.openExtension` and
  `Scheme.IdealSheafData.comap_openExtension`: the canonical quasi-coherent extension
  of an ideal sheaf from a retrocompact open, with its restriction identity
  (Stacks Project Tag 01PE, ideal form; blueprint §1.2.A), realized as the kernel of
  `Z_J ↪ W ↪ X` and computed by flat base change of scheme-theoretic images;
- `Scheme.IdealSheafData.exists_finiteType_le_comap_eq`: the finite-type refinement
  (Stacks Project Tag 01PF, blueprint §1.2.B–C): every ideal sheaf on a qcqs scheme
  whose restriction to a quasi-compact open `W` is of finite type contains a
  finite-type ideal sheaf with the same restriction to `W`. The binary gluing step is
  `Scheme.IdealSheafData.exists_le_finiteTypeOn_sup`: the glued ideal sheaf is the
  intersection of the maximal quasi-coherent extensions (`IdealSheafData.map` along
  the two inclusions) of the current ideal sheaf and of the clearing-denominators
  approximation `Ideal.exists_fg_le_map_localization_eq` on the new affine piece,
  intersected with the ambient ideal sheaf; a finite induction over an affine cover
  concludes. The supporting interface comprises the base-change lemma
  `Scheme.IdealSheafData.map_comap_opens`, the `appLE` ideal computation
  `Scheme.IdealSheafData.ideal_comap_ι_eq_map_appLE`, the covering comparison lemma
  `Scheme.IdealSheafData.comap_le_comap_of_ideal_le` and the finite-typeness locality
  `Scheme.IdealSheafData.FiniteTypeOn.sup`.

These provide the inputs for the Stacks Tags 01PF and 01PH statements
(`Scheme.exists_finiteType_ideal_extension`,
`Scheme.exists_finiteType_ideal_zeroLocus_compl_qcOpen`) proved in
`WeilConjectures.Blowup.Admissible`.

-/

@[expose] public section

universe u

namespace AlgebraicGeometry

section OpenExtension

open CategoryTheory Limits

variable {X : Scheme.{u}} (W : X.Opens)

variable (J : W.toScheme.IdealSheafData)

/-- **The canonical quasi-coherent extension of an ideal sheaf from an open**
(Stacks Project Tag 01PE, ideal form; blueprint §1.2.A): the kernel of the composite
of the closed subscheme of `J` with the open immersion `W.ι`. Its restriction back to
`W` is `J` (`Scheme.IdealSheafData.comap_openExtension`); it is quasi-coherent by
construction, but not finite type in general — the finite-type refinement is
Tag 01PF. -/
noncomputable def Scheme.IdealSheafData.openExtension : X.IdealSheafData :=
  (J.subschemeι ≫ W.ι).ker

/-- **The canonical extension restricts to the original ideal** (Stacks Project
Tag 01PE): pulling the extension back along the quasi-compact open immersion recovers
`J`. The proof identifies the restriction of the kernel with the kernel of the closed
immersion of `J` via flat base change of scheme-theoretic images
(`Scheme.Hom.ker_pullback_snd`). -/
theorem Scheme.IdealSheafData.comap_openExtension [QuasiCompact W.ι] :
    (Scheme.IdealSheafData.openExtension W J).comap W.ι = J := by
  rw [Scheme.IdealSheafData.openExtension,
    ← AlgebraicGeometry.Scheme.Hom.ker_pullback_snd (J.subschemeι ≫ W.ι) W.ι]
  have H : IsPullback (𝟙 J.subscheme) J.subschemeι (J.subschemeι ≫ W.ι) W.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp]⟩
  have hsnd : pullback.snd (J.subschemeι ≫ W.ι) W.ι =
      H.isoPullback.inv ≫ J.subschemeι :=
    ((Iso.inv_comp_eq _).mpr H.isoPullback_hom_snd.symm).symm
  rw [hsnd, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- The canonical extension is monotone in the ideal sheaf. -/
theorem Scheme.IdealSheafData.openExtension_mono {K K' : W.toScheme.IdealSheafData}
    (h : K ≤ K') :
    Scheme.IdealSheafData.openExtension W K ≤ Scheme.IdealSheafData.openExtension W K' := by
  have hfac : K'.subschemeι ≫ W.ι =
      Scheme.IdealSheafData.inclusion h ≫ (K.subschemeι ≫ W.ι) := by
    rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]
  calc Scheme.IdealSheafData.openExtension W K = (K.subschemeι ≫ W.ι).ker := rfl
    _ ≤ (Scheme.IdealSheafData.inclusion h ≫ (K.subschemeι ≫ W.ι)).ker :=
        Scheme.Hom.le_ker_comp _ _
    _ = Scheme.IdealSheafData.openExtension W K' := by
        rw [← hfac]
        rfl

/-- Every ideal sheaf is contained in the canonical extension of its own restriction:
sections of `I₀` pull back to sections vanishing on the subscheme of the
restriction. -/
theorem Scheme.IdealSheafData.le_openExtension_comap (I₀ : X.IdealSheafData) :
    I₀ ≤ Scheme.IdealSheafData.openExtension W (I₀.comap W.ι) := by
  have hfac : (I₀.comap W.ι).subschemeι ≫ W.ι =
      (I₀.comapIso W.ι).hom ≫ (pullback.snd W.ι I₀.subschemeι ≫ I₀.subschemeι) := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition]
  calc I₀ = I₀.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι I₀).symm
    _ ≤ (pullback.snd W.ι I₀.subschemeι ≫ I₀.subschemeι).ker := Scheme.Hom.le_ker_comp _ _
    _ = ((I₀.comapIso W.ι).hom ≫ (pullback.snd W.ι I₀.subschemeι ≫ I₀.subschemeι)).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = Scheme.IdealSheafData.openExtension W (I₀.comap W.ι) := by
        rw [← hfac]
        rfl

/-- **The extension adjunction**: an ideal sheaf is contained in the canonical
extension of `K` if and only if its restriction is contained in `K`. This is the
order-theoretic form of the gluing argument: containment in the extension is exactly a
condition on the restriction. -/
theorem Scheme.IdealSheafData.le_openExtension_iff [QuasiCompact W.ι]
    (I₀ : X.IdealSheafData) (K : W.toScheme.IdealSheafData) :
    I₀ ≤ Scheme.IdealSheafData.openExtension W K ↔ I₀.comap W.ι ≤ K := by
  constructor
  · intro h
    have h2 : I₀.comap W.ι ≤ (Scheme.IdealSheafData.openExtension W K).comap W.ι :=
      Scheme.IdealSheafData.comap_mono W.ι h
    rwa [Scheme.IdealSheafData.comap_openExtension] at h2
  · intro h
    exact (Scheme.IdealSheafData.le_openExtension_comap W I₀).trans
      (Scheme.IdealSheafData.openExtension_mono W h)

/-- Finite-typeness of an ideal sheaf on the affine opens contained in a given open.
`FiniteTypeOn ⊤` is finite-typeness (`Scheme.IdealSheafData.FiniteType` of
`WeilConjectures.Blowup.Exceptional`). -/
def Scheme.IdealSheafData.FiniteTypeOn (O : X.Opens) (I : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ↑U ≤ O → (I.ideal U).FG

/-- **The canonical extension is finite type on the open it extends from**: if `J` is
a finite-type ideal sheaf on `W`, then `openExtension W J` has finitely generated
ideals of sections on every affine open contained in `W`. -/
theorem Scheme.IdealSheafData.finiteTypeOn_openExtension [QuasiCompact W.ι]
    (hJ : ∀ U' : W.toScheme.affineOpens, (J.ideal U').FG) :
    (Scheme.IdealSheafData.openExtension W J).FiniteTypeOn W := by
  intro U hU
  have hle : U.1 ≤ W.ι.opensRange := by
    rwa [Scheme.Opens.opensRange_ι]
  set U' : W.toScheme.affineOpens := ⟨W.ι ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion W.ι hle⟩
    with hU'def
  have himg : W.ι ''ᵁ (U' : W.toScheme.Opens) = U.1 := by
    rw [hU'def, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hU]
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion
    (Scheme.IdealSheafData.openExtension W J) W.ι U'
  rw [Scheme.IdealSheafData.comap_openExtension] at h1
  have hbij : Function.Bijective ((W.ι.appIso (U' : W.toScheme.Opens)).inv.hom) :=
    ConcreteCategory.bijective_of_isIso _
  have h2 := congrArg (Ideal.map ((W.ι.appIso (U' : W.toScheme.Opens)).inv.hom)) h1
  rw [Ideal.map_comap_of_surjective _ hbij.2] at h2
  have hcongr : (⟨W.ι ''ᵁ (U' : W.toScheme.Opens),
      U'.2.image_of_isOpenImmersion W.ι⟩ : X.affineOpens) = U := Subtype.ext himg
  rw [← hcongr, ← h2]
  exact (hJ U').map _

end OpenExtension

section FiniteTypeGluing

/-! ### The finite-type refinement (Stacks Project Tag 01PF)

This section proves the finite-type refinement of the quasi-coherent extension: on a qcqs
scheme, every ideal sheaf whose restriction to a quasi-compact open `W` is of finite type
contains a finite-type ideal sheaf with the same restriction to `W`
(`Scheme.IdealSheafData.exists_finiteType_le_comap_eq`).

The proof follows the blueprint (§1.2.B–C of
`blueprint/src/version/detailed/nagata/nagata_new_proof_order.md`): a binary gluing step
(`exists_le_finiteTypeOn_sup`) enlarges the open of finite-typeness by one affine open at a
time, using the affine clearing-denominators lemma `Ideal.exists_fg_le_map_localization_eq`
on a finite basic-open cover of the overlap, and a finite induction over an affine cover
concludes. The gluing itself is order-theoretic: the glued ideal sheaf is the intersection
of the pushforwards (maximal quasi-coherent extensions) of the two local pieces with the
ambient ideal sheaf, and its restrictions are computed via the flat base change of
scheme-theoretic images (`Scheme.Hom.ker_pullback_snd`). -/

open CategoryTheory Limits

variable {X : Scheme.{u}}

/-- Pullback of ideal sheaves along an open immersion commutes with intersections. -/
lemma Scheme.IdealSheafData.comap_inf_of_isOpenImmersion {Z T : Scheme.{u}} (j : Z ⟶ T)
    [IsOpenImmersion j] (I K : T.IdealSheafData) :
    (I ⊓ K).comap j = I.comap j ⊓ K.comap j := by
  ext U : 2
  simp only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Ideal.comap_inf]

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion,
computed on an affine open of the source lying over an affine open `V` of the target: it
is the extension of the ideal of sections on `V` along the restriction map `appLE`. -/
lemma Scheme.IdealSheafData.ideal_comap_eq_map_appLE {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (C : Z.IdealSheafData) (V : Z.affineOpens) (U' : Y.affineOpens)
    (h : U'.1 ≤ f ⁻¹ᵁ V.1) :
    (C.comap f).ideal U' = (C.ideal V).map (f.appLE V.1 U'.1 h).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have himg : (⟨f ''ᵁ U'.1, U'.2.image_of_isOpenImmersion f⟩ : Z.affineOpens) ≤ V := by
    change f ''ᵁ U'.1 ≤ V.1
    refine (f.image_mono h).trans ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  rw [← Scheme.IdealSheafData.map_ideal C himg, CommRingCat.ideal_comap_inv_hom,
    Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- The special case of `Scheme.IdealSheafData.ideal_comap_eq_map_appLE` for the
inclusion of an affine open. -/
lemma Scheme.IdealSheafData.ideal_comap_ι_eq_map_appLE (I : X.IdealSheafData)
    (V : X.affineOpens) (U' : V.1.toScheme.affineOpens) (h : U'.1 ≤ V.1.ι ⁻¹ᵁ V.1) :
    (I.comap V.1.ι).ideal U' = (I.ideal V).map (V.1.ι.appLE V.1 U'.1 h).hom :=
  Scheme.IdealSheafData.ideal_comap_eq_map_appLE V.1.ι I V U' h

/-- To compare two pullbacks of ideal sheaves along an open immersion, it suffices to
compare the ideals of sections on a family of affine opens contained in the range whose
preimages cover the source. -/
lemma Scheme.IdealSheafData.comap_le_comap_of_ideal_le {Z T : Scheme.{u}} (j : Z ⟶ T)
    [IsOpenImmersion j] {I K : T.IdealSheafData} {ι : Type*} (U : ι → T.affineOpens)
    (hran : ∀ i, (U i).1 ≤ j.opensRange) (hcov : j.opensRange ≤ ⨆ i, (U i).1)
    (H : ∀ i, I.ideal (U i) ≤ K.ideal (U i)) :
    I.comap j ≤ K.comap j := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun i ↦ ⟨j ⁻¹ᵁ (U i).1, (U i).2.preimage_of_isOpenImmersion j (hran i)⟩) ?_ (fun i ↦ ?_)
  · rw [eq_top_iff]
    intro x _
    have hx : j x ∈ j.opensRange := ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    refine Ideal.comap_mono ?_
    have hcongr : (⟨j ''ᵁ (j ⁻¹ᵁ (U i).1),
        ((U i).2.preimage_of_isOpenImmersion j (hran i)).image_of_isOpenImmersion j⟩ :
        T.affineOpens) = U i :=
      Subtype.ext (by
        change j ''ᵁ (j ⁻¹ᵁ (U i).1) = (U i).1
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hran i)])
    have h := H i
    rw [← hcongr] at h
    exact h

/-- The pushforward of an ideal sheaf along the inclusion of a quasi-compact open
restricts back to the original ideal sheaf. This is
`Scheme.IdealSheafData.comap_openExtension` in `map`/`comap` language. -/
theorem Scheme.IdealSheafData.comap_map_ι (W : X.Opens) [QuasiCompact W.ι]
    (J : W.toScheme.IdealSheafData) : (J.map W.ι).comap W.ι = J :=
  Scheme.IdealSheafData.comap_openExtension W J

/-- **Base change of ideal sheaf pushforwards to open subschemes**: for a quasi-compact
morphism `g`, the restriction of the pushforward `g_* B` to an open `O` is the pushforward
of the restriction of `B` to `g ⁻¹ᵁ O` along the restricted morphism. This is the flat
base change of scheme-theoretic images (`Scheme.Hom.ker_pullback_snd`) in ideal sheaf
form. -/
theorem Scheme.IdealSheafData.map_comap_opens {Y : Scheme.{u}} (g : Y ⟶ X) [QuasiCompact g]
    (B : Y.IdealSheafData) (O : X.Opens) :
    (B.map g).comap O.ι = (B.comap (g ⁻¹ᵁ O).ι).map (g ∣_ O) := by
  have hker : ∀ {Z W : Scheme.{u}} (C : Z.IdealSheafData) (φ : Z ⟶ W),
      C.map φ = (C.subschemeι ≫ φ).ker := fun C φ ↦ by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  have H := ((IsPullback.of_hasPullback (g ⁻¹ᵁ O).ι B.subschemeι).paste_horiz
    (isPullback_morphismRestrict g O)).flip
  rw [hker B g, hker (B.comap (g ⁻¹ᵁ O).ι) (g ∣_ O),
    ← Scheme.Hom.ker_pullback_snd (B.subschemeι ≫ g) O.ι]
  have hsub : (B.comap (g ⁻¹ᵁ O).ι).subschemeι =
      (B.comapIso (g ⁻¹ᵁ O).ι).hom ≫ pullback.fst (g ⁻¹ᵁ O).ι B.subschemeι :=
    (Scheme.IdealSheafData.comapIso_hom_fst _ _).symm
  rw [hsub, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- An ideal sheaf whose restriction to `W` is of finite type is of finite type on the
affine opens contained in `W`. -/
theorem Scheme.IdealSheafData.finiteTypeOn_of_comap {W : X.Opens} {I : X.IdealSheafData}
    (hJ : ∀ U' : W.toScheme.affineOpens, ((I.comap W.ι).ideal U').FG) :
    I.FiniteTypeOn W := by
  intro U hU
  have hle : U.1 ≤ W.ι.opensRange := by
    rwa [Scheme.Opens.opensRange_ι]
  set U' : W.toScheme.affineOpens := ⟨W.ι ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion W.ι hle⟩
    with hU'def
  have himg : W.ι ''ᵁ (U' : W.toScheme.Opens) = U.1 := by
    rw [hU'def, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hU]
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I W.ι U'
  have hbij : Function.Bijective ((W.ι.appIso (U' : W.toScheme.Opens)).inv.hom) :=
    ConcreteCategory.bijective_of_isIso _
  have h2 := congrArg (Ideal.map ((W.ι.appIso (U' : W.toScheme.Opens)).inv.hom)) h1
  rw [Ideal.map_comap_of_surjective _ hbij.2] at h2
  have hcongr : (⟨W.ι ''ᵁ (U' : W.toScheme.Opens),
      U'.2.image_of_isOpenImmersion W.ι⟩ : X.affineOpens) = U := Subtype.ext himg
  rw [← hcongr, ← h2]
  exact (hJ U').map _

/-- Conversely, the restriction to `W` of an ideal sheaf which is of finite type on the
affine opens contained in `W` is of finite type. -/
theorem Scheme.IdealSheafData.fg_ideal_comap_of_finiteTypeOn {W : X.Opens}
    {I : X.IdealSheafData} (h : I.FiniteTypeOn W) (U' : W.toScheme.affineOpens) :
    ((I.comap W.ι).ideal U').FG := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, CommRingCat.ideal_comap_inv_hom]
  exact (h ⟨W.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion W.ι⟩ (W.ι_image_le U'.1)).map _

/-- **Locality of finite-typeness**: an ideal sheaf which is of finite type on two opens is
of finite type on their union. On a straddling affine open, the ideal of sections is
finitely generated because its localizations at a spanning family of sections are
(`Ideal.fg_of_localizationSpan`). -/
theorem Scheme.IdealSheafData.FiniteTypeOn.sup {I : X.IdealSheafData} {O₁ O₂ : X.Opens}
    (h₁ : I.FiniteTypeOn O₁) (h₂ : I.FiniteTypeOn O₂) :
    I.FiniteTypeOn (O₁ ⊔ O₂) := by
  intro U hU
  have hspan : Ideal.span {f : Γ(X, U.1) | X.basicOpen f ≤ O₁ ∨ X.basicOpen f ≤ O₂} = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hxU
    rcases TopologicalSpace.Opens.mem_sup.mp (hU hxU) with hx | hx
    · obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (⟨x, hx⟩ : O₁) hxU
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, Or.inl hf⟩, hxf⟩
    · obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (⟨x, hx⟩ : O₂) hxU
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, Or.inr hf⟩, hxf⟩
  refine Ideal.fg_of_localizationSpan _ hspan fun g ↦ ?_
  have hfg : (I.ideal (X.affineBasicOpen g.1)).FG := by
    rcases g.2 with hg | hg
    · exact h₁ (X.affineBasicOpen g.1) ((X.affineBasicOpen_coe g.1).trans_le hg)
    · exact h₂ (X.affineBasicOpen g.1) ((X.affineBasicOpen_coe g.1).trans_le hg)
  have := U.2.isLocalization_basicOpen g.1
  refine Ideal.FG.map_localizationAway (S := Γ(X, X.basicOpen g.1)) ?_
  rw [show algebraMap Γ(X, U.1) Γ(X, X.basicOpen g.1) =
      (X.presheaf.map (homOfLE <| X.basicOpen_le g.1).op).hom from rfl,
    I.map_ideal_basicOpen U g.1]
  exact hfg

/-- **The binary gluing step of the finite-type extension theorem** (Stacks Project
Tag 01PF; blueprint §1.2.C): if `I₀ ≤ H₀` is of finite type on the affine opens contained
in a quasi-compact open `O`, there is an `I ≤ H₀` of finite type on the affine opens
contained in `O ⊔ V`, for `V` affine, with the same restriction to `O`.

The new ideal sheaf is `((I₀|_O)_* ) ⊓ ((Ñ')_*) ⊓ H₀` where `N' ≤ N = I₀(V)` is the
finitely generated subideal produced by the affine clearing-denominators lemma on a finite
basic-open cover of the overlap `O ⊓ V`, and the pushforwards are the maximal
quasi-coherent extensions from `O` resp. `V`. -/
theorem Scheme.IdealSheafData.exists_le_finiteTypeOn_sup [QuasiSeparatedSpace X]
    {H₀ I₀ : X.IdealSheafData} {O : X.Opens} (hO : IsCompact (O : Set X))
    (V : X.affineOpens) (hle : I₀ ≤ H₀) (hft : I₀.FiniteTypeOn O) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.FiniteTypeOn (O ⊔ V.1) ∧
      I.comap O.ι = I₀.comap O.ι := by
  classical
  have hOι : QuasiCompact O.ι := Scheme.Opens.quasiCompact_ι O hO
  have hVι : QuasiCompact V.1.ι := Scheme.Opens.quasiCompact_ι V.1 V.2.isCompact
  have : IsAffine V.1.toScheme := V.2
  set N : Ideal Γ(X, V.1) := I₀.ideal V with hNdef
  -- a finite basic-open cover of the overlap `O ⊓ V`
  have hOV : IsCompact ((O ⊓ V.1 : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ O.isOpen hO V.1.isOpen V.2.isCompact
  obtain ⟨s0, hs0⟩ := hOV.elim_finite_subcover
    (fun f : {f : Γ(X, V.1) // X.basicOpen f ≤ O ⊓ V.1} ↦ (X.basicOpen f.1 : Set X))
    (fun f ↦ (X.basicOpen f.1).isOpen)
    (by
      intro x hx
      obtain ⟨f, hf, hxf⟩ := V.2.exists_basicOpen_le (⟨x, hx⟩ : (O ⊓ V.1 : X.Opens))
        (TopologicalSpace.Opens.mem_inf.mp hx).2
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩)
  set s : Finset Γ(X, V.1) := s0.image (·.1) with hsdef
  have hsub : ∀ f ∈ s, X.basicOpen f ≤ O ⊓ V.1 := by
    intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hf
    exact g.2
  -- clearing denominators: a finitely generated `N' ≤ N` with the same localizations
  have hlocfg : ∀ f ∈ s, (N.map (algebraMap Γ(X, V.1) (Localization.Away f))).FG := by
    intro f hf
    have := V.2.isLocalization_basicOpen f
    have hfg : (I₀.ideal (X.affineBasicOpen f)).FG :=
      hft (X.affineBasicOpen f)
        ((X.affineBasicOpen_coe f).trans_le ((hsub f hf).trans inf_le_left))
    refine Ideal.FG.map_localizationAway (S := Γ(X, X.basicOpen f)) ?_
    rw [show algebraMap Γ(X, V.1) Γ(X, X.basicOpen f) =
        (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom from rfl,
      I₀.map_ideal_basicOpen V f]
    exact hfg
  obtain ⟨N', hN'le, hN'fg, hN'loc⟩ := N.exists_fg_le_map_localization_eq s hlocfg
  -- the finite-type ideal sheaf on `V` generated by `N'`
  have htop : (⊤ : V.1.toScheme.Opens) ≤ V.1.ι ⁻¹ᵁ V.1 := V.1.ι_preimage_self.ge
  set K' : V.1.toScheme.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop (N'.map (V.1.ι.appLE V.1 ⊤ htop).hom) with hK'def
  have hK'ideal : ∀ U'' : V.1.toScheme.affineOpens,
      K'.ideal U'' = N'.map (V.1.ι.appLE V.1 U''.1 (le_top.trans htop)).hom := by
    intro U''
    rw [hK'def, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.Hom.appLE_map]
  have hIdealV : ∀ (L : X.IdealSheafData) (U'' : V.1.toScheme.affineOpens),
      (L.comap V.1.ι).ideal U'' =
        (L.ideal V).map (V.1.ι.appLE V.1 U''.1 (le_top.trans htop)).hom :=
    fun L U'' ↦ L.ideal_comap_ι_eq_map_appLE V U'' _
  have hK'le : K' ≤ I₀.comap V.1.ι := by
    refine Scheme.IdealSheafData.le_of_isAffine ?_
    rw [hK'ideal ⟨⊤, isAffineOpen_top _⟩, hIdealV I₀ ⟨⊤, isAffineOpen_top _⟩]
    exact Ideal.map_mono hN'le
  -- the comparison on the overlap: `I₀` and `K'` restrict to the same ideal sheaf
  have hpre : IsAffineOpen (V.1.ι ⁻¹ᵁ V.1) :=
    V.2.preimage_of_isOpenImmersion V.1.ι (by rw [Scheme.Opens.opensRange_ι])
  have hoverlap : (I₀.comap V.1.ι).comap (V.1.ι ⁻¹ᵁ O).ι ≤ K'.comap (V.1.ι ⁻¹ᵁ O).ι := by
    refine Scheme.IdealSheafData.comap_le_comap_of_ideal_le _
      (fun f : s ↦ ⟨V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1),
        hpre.basicOpen (V.1.ι.app V.1 f.1)⟩) (fun f ↦ ?_) ?_ (fun f ↦ ?_)
    · rw [Scheme.Opens.opensRange_ι]
      change V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1) ≤ V.1.ι ⁻¹ᵁ O
      rw [← Scheme.preimage_basicOpen]
      intro x hx
      exact ((hsub f.1 f.2).trans inf_le_left) hx
    · rw [Scheme.Opens.opensRange_ι]
      intro x hx
      have hxV : V.1.ι x ∈ (V.1 : Set X) := by
        rw [← Scheme.Opens.range_ι (U := V.1)]
        exact Set.mem_range_self x
      obtain ⟨g, hg0, hxg⟩ := Set.mem_iUnion₂.mp (hs0 ⟨hx, hxV⟩)
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g.1, Finset.mem_image_of_mem _ hg0⟩, ?_⟩
      change x ∈ V.1.toScheme.basicOpen (V.1.ι.app V.1 g.1)
      rwa [← Scheme.preimage_basicOpen]
    · rw [hIdealV I₀, hK'ideal]
      refine le_of_eq ?_
      have hunit : IsUnit ((V.1.ι.appLE V.1
          (V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1)) (le_top.trans htop)).hom f.1) := by
        have := hpre.isLocalization_basicOpen (V.1.ι.app V.1 f.1)
        have heq : (V.1.ι.appLE V.1
            (V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1)) (le_top.trans htop)).hom f.1 =
            algebraMap Γ(V.1.toScheme, V.1.ι ⁻¹ᵁ V.1)
              Γ(V.1.toScheme, V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1))
              (V.1.ι.app V.1 f.1) := rfl
        rw [heq]
        exact IsLocalization.map_units _ ⟨_, Submonoid.mem_powers (V.1.ι.app V.1 f.1)⟩
      exact Ideal.map_eq_map_of_localizationAway hunit ((hN'loc f.1 f.2).symm)
  -- the two maximal extensions and the candidate ideal sheaf
  set F₁ : X.IdealSheafData := (I₀.comap O.ι).map O.ι with hF₁def
  set F₂ : X.IdealSheafData := K'.map V.1.ι with hF₂def
  have hAleF₂ : I₀.comap O.ι ≤ F₂.comap O.ι := by
    rw [hF₂def, Scheme.IdealSheafData.map_comap_opens V.1.ι K' O,
      Scheme.IdealSheafData.le_map_iff_comap_le]
    have hcomp : (I₀.comap O.ι).comap (V.1.ι ∣_ O) =
        (I₀.comap V.1.ι).comap (V.1.ι ⁻¹ᵁ O).ι := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        morphismRestrict_ι]
    rwa [hcomp]
  have hcomapO : (F₁ ⊓ F₂ ⊓ H₀).comap O.ι = I₀.comap O.ι := by
    rw [Scheme.IdealSheafData.comap_inf_of_isOpenImmersion,
      Scheme.IdealSheafData.comap_inf_of_isOpenImmersion, hF₁def,
      Scheme.IdealSheafData.comap_map_ι, inf_eq_left.mpr hAleF₂,
      inf_eq_left.mpr (Scheme.IdealSheafData.comap_mono O.ι hle)]
  have hcomapV : (F₁ ⊓ F₂ ⊓ H₀).comap V.1.ι = K' := by
    rw [Scheme.IdealSheafData.comap_inf_of_isOpenImmersion,
      Scheme.IdealSheafData.comap_inf_of_isOpenImmersion, hF₂def,
      Scheme.IdealSheafData.comap_map_ι]
    have h1 : K' ≤ F₁.comap V.1.ι :=
      hK'le.trans (Scheme.IdealSheafData.comap_mono V.1.ι
        (Scheme.IdealSheafData.le_map_comap I₀ O.ι))
    have h2 : K' ≤ H₀.comap V.1.ι :=
      hK'le.trans (Scheme.IdealSheafData.comap_mono V.1.ι hle)
    rw [inf_eq_right.mpr h1, inf_eq_left.mpr h2]
  refine ⟨F₁ ⊓ F₂ ⊓ H₀, inf_le_right, Scheme.IdealSheafData.FiniteTypeOn.sup ?_ ?_, hcomapO⟩
  · refine Scheme.IdealSheafData.finiteTypeOn_of_comap fun U'' ↦ ?_
    rw [hcomapO]
    exact Scheme.IdealSheafData.fg_ideal_comap_of_finiteTypeOn hft U''
  · refine Scheme.IdealSheafData.finiteTypeOn_of_comap fun U'' ↦ ?_
    rw [hcomapV, hK'ideal U'']
    exact hN'fg.map _

/-- **Existence of a finite-type ideal sheaf with prescribed restriction** (Stacks Project
Tag 01PF, order-theoretic form; blueprint §1.2): on a quasi-compact quasi-separated scheme,
every ideal sheaf `H₀` whose restriction to a quasi-compact open `W` is of finite type
contains a finite-type ideal sheaf with the same restriction to `W`. -/
theorem Scheme.IdealSheafData.exists_finiteType_le_comap_eq [CompactSpace X]
    [QuasiSeparatedSpace X] (H₀ : X.IdealSheafData) (W : X.Opens)
    (hW : IsCompact (W : Set X))
    (hJ : ∀ U' : W.toScheme.affineOpens, ((H₀.comap W.ι).ideal U').FG) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ (∀ U : X.affineOpens, (I.ideal U).FG) ∧
      I.comap W.ι = H₀.comap W.ι := by
  classical
  have key : ∀ t : Finset X.affineOpens,
      IsCompact ((W ⊔ t.sup (fun V ↦ V.1) : X.Opens) : Set X) ∧
      ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.FiniteTypeOn (W ⊔ t.sup (fun V ↦ V.1)) ∧
        I.comap W.ι = H₀.comap W.ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty, sup_bot_eq]
      exact ⟨hW, H₀, le_rfl, Scheme.IdealSheafData.finiteTypeOn_of_comap hJ, rfl⟩
    | insert V t hV IH =>
      obtain ⟨hO, I₀, hle, hft, hcomap⟩ := IH
      have hsup : W ⊔ (insert V t).sup (fun V ↦ V.1) =
          (W ⊔ t.sup (fun V ↦ V.1)) ⊔ V.1 := by
        rw [Finset.sup_insert, sup_comm V.1 (t.sup fun V ↦ V.1), ← sup_assoc]
      constructor
      · rw [hsup, TopologicalSpace.Opens.coe_sup]
        exact hO.union V.2.isCompact
      obtain ⟨I, hIle, hIft, hIcomap⟩ :=
        Scheme.IdealSheafData.exists_le_finiteTypeOn_sup hO V hle hft
      refine ⟨I, hIle, by rwa [hsup], ?_⟩
      have hWle : W ≤ W ⊔ t.sup (fun V ↦ V.1) := le_sup_left
      have h1 : I.comap W.ι =
          (I.comap (W ⊔ t.sup (fun V ↦ V.1)).ι).comap (X.homOfLE hWle) := by
        rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
      have h2 : I₀.comap W.ι =
          (I₀.comap (W ⊔ t.sup (fun V ↦ V.1)).ι).comap (X.homOfLE hWle) := by
        rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
      rw [h1, hIcomap, ← h2, hcomap]
  have hcov : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨V, hV⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) hcov
  obtain ⟨-, I, hle, hft, hcomap⟩ := key t
  refine ⟨I, hle, fun U ↦ hft U fun x _ ↦ ?_, hcomap⟩
  obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact (le_sup_right : t.sup (fun V ↦ V.1) ≤ W ⊔ t.sup (fun V ↦ V.1))
    ((Finset.le_sup (f := fun V ↦ V.1) hVt) hxV)

end FiniteTypeGluing

end AlgebraicGeometry
