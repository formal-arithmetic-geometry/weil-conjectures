/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.SeparatingPair
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Separatedness descends to a finite stage

If the limit of a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps is separated, then so is every stage past some stage
(`AlgebraicGeometry.Scheme.exists_isSeparated_of_isLimit`, Stacks Project Tag 086Q), and the
relative version over a base (`AlgebraicGeometry.Scheme.exists_isSeparated_app_of_isLimit`,
Stacks Project Tag 01ZH).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section SeparatedDescent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

set_option maxHeartbeats 1000000 in
-- the reduction to the affine criterion goes through two common refinements of stages
include hc in
/-- **Separatedness descends to a finite stage.**

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes with affine
transition maps. If `lim Dᵢ` is separated, then `Dᵢ` is separated for every `i` past some stage.
(Blueprint: `lemma:nagata-fixed-base-separated-stage-exists`.) -/
@[stacks 086Q]
theorem Scheme.exists_isSeparated_of_isLimit [c.pt.IsSeparated] :
    ∃ i₀ : I, ∀ {i : I} (_ : i ⟶ i₀), (D.obj i).IsSeparated := by
  classical
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : ∀ i, IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc
  set 𝒰 := (D.obj i₀).affineCover.finiteSubcover with h𝒰
  have h𝒰aff : ∀ a : 𝒰.I₀, IsAffine (𝒰.X a) := fun a ↦ inferInstanceAs (IsAffine (Spec _))
  set U : 𝒰.I₀ → (D.obj i₀).Opens := fun a ↦ (𝒰.f a).opensRange with hU
  have haff : ∀ a, IsAffineOpen (U a) := fun a ↦ isAffineOpen_opensRange _
  have hcov : TopologicalSpace.IsOpenCover U := 𝒰.isOpenCover_opensRange
  have hcpt : ∀ a b, IsCompact ((U a ⊓ U b : (D.obj i₀).Opens) : Set (D.obj i₀)) := fun a b ↦
    isQuasiSeparated_univ _ _ (Set.subset_univ _) (U a).2 (haff a).isCompact
      (Set.subset_univ _) (U b).2 (haff b).isCompact
  have haffLim : ∀ a, IsAffineOpen (c.π.app i₀ ⁻¹ᵁ U a) := fun a ↦ (haff a).preimage _
  have haffLimInf : ∀ a b, IsAffineOpen (c.π.app i₀ ⁻¹ᵁ (U a ⊓ U b)) := fun a b ↦
    IsAffineOpen.inf (X := c.pt) (haffLim a) (haffLim b)
  -- pass to a stage where all the (finitely many) intersections are affine
  have hstage : ∀ a b, ∃ j : Over i₀, IsAffineOpen (D.map j.hom ⁻¹ᵁ (U a ⊓ U b)) := fun a b ↦
    exists_isAffineOpen_preimage hc (hcpt a b) (haffLimInf a b)
  choose jj hjj using hstage
  cases nonempty_fintype 𝒰.I₀
  obtain ⟨i₁, hi₁⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : 𝒰.I₀ × 𝒰.I₀ ↦ jj p.1 p.2) Finset.univ)
  set U' : 𝒰.I₀ → (D.obj i₁.left).Opens := fun a ↦ D.map i₁.hom ⁻¹ᵁ U a with hU'
  have haff' : ∀ a, IsAffineOpen (U' a) := fun a ↦ (haff a).preimage _
  have haffInf' : ∀ a b, IsAffineOpen (U' a ⊓ U' b) := by
    intro a b
    obtain ⟨m⟩ := hi₁ (Finset.mem_image_of_mem _ (Finset.mem_univ (a, b)))
    have : (U' a ⊓ U' b : (D.obj i₁.left).Opens)
        = D.map m.left ⁻¹ᵁ (D.map (jj a b).hom ⁻¹ᵁ (U a ⊓ U b)) := by
      rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w m]
      rfl
    rw [this]
    exact (hjj a b).preimage _
  have hcov' : TopologicalSpace.IsOpenCover U' := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [hU']
    rw [← Scheme.Hom.preimage_iSup, hcov.iSup_eq_top, Scheme.Hom.preimage_top]
  -- the pairs separate in the limit
  have hsep : ∀ a b, IsSeparatingPair c.pt (c.π.app i₁.left ⁻¹ᵁ U' a) (c.π.app i₁.left ⁻¹ᵁ U' b) :=
    fun a b ↦ isSeparatingPair_of_isSeparated ((haff' a).preimage _) ((haff' b).preimage _)
  have hpair : ∀ a b, ∃ j : Over i₁.left, ∀ {k : Over i₁.left} (_ : k ⟶ j),
      IsSeparatingPair (D.obj k.left) (D.map k.hom ⁻¹ᵁ U' a) (D.map k.hom ⁻¹ᵁ U' b) := fun a b ↦
    exists_isSeparatingPair_of_isLimit hc i₁.left (haff' a) (haff' b) (haffInf' a b) (hsep a b)
  choose kk hkk using hpair
  obtain ⟨kstar, hkstar⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun p : 𝒰.I₀ × 𝒰.I₀ ↦ kk p.1 p.2) Finset.univ)
  refine ⟨kstar.left, ?_⟩
  intro i g
  set k : Over i₁.left := Over.mk (g ≫ kstar.hom) with hk
  have gk : k ⟶ kstar := Over.homMk g
  refine Scheme.isSeparated_of_isSeparatingPair (fun a ↦ D.map k.hom ⁻¹ᵁ U' a) ?_
    (fun a ↦ (haff' a).preimage _) (fun a b ↦ (haffInf' a b).preimage _) ?_
  · refine TopologicalSpace.IsOpenCover.mk ?_
    rw [← Scheme.Hom.preimage_iSup, hcov'.iSup_eq_top, Scheme.Hom.preimage_top]
  · intro a b
    obtain ⟨m⟩ := hkstar (Finset.mem_image_of_mem _ (Finset.mem_univ (a, b)))
    exact hkk a b (gk ≫ m)

variable {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) [∀ i, QuasiCompact (t.app i)]

set_option maxHeartbeats 1000000 in
-- the reduction to the absolute case goes through a finite affine cover of the image
include hc in
/-- **Separatedness over a fixed base descends to a finite stage.**

Let `{Dᵢ}` be a cofiltered inverse system of quasi-compact quasi-separated schemes over a base
`S`, with affine transition maps and quasi-compact structure morphisms. If `lim Dᵢ ⟶ S` is
separated, then `Dᵢ ⟶ S` is separated for every `i` past some stage.
(Blueprint: `lemma:nagata-fixed-base-separated-eventually`.) -/
@[stacks 01ZH]
theorem Scheme.exists_isSeparated_app_of_isLimit (i₀ : I)
    [IsSeparated (c.π.app i₀ ≫ t.app i₀)] :
    ∃ j : I, ∀ {i : I} (_ : i ⟶ j), IsSeparated (t.app i) := by
  classical
  set f : c.pt ⟶ S := c.π.app i₀ ≫ t.app i₀ with hf
  -- finitely many affine opens of `S` covering the image of `D.obj i₀`
  have hcpt : IsCompact (Set.range ⇑(t.app i₀).base) := isCompact_range (t.app i₀).continuous
  obtain ⟨s, hs⟩ := hcpt.elim_finite_subcover (fun V : S.affineOpens ↦ (V : Set S))
    (fun V ↦ (V : S.Opens).2) (by
      intro x _
      have : x ∈ (⊤ : S.Opens) := trivial
      rw [← iSup_affineOpens_eq_top S] at this
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp this
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- for every affine open of `S`, the preimages become separated at some stage
  have hstage : ∀ V : S.affineOpens, ∃ j : Over i₀, ∀ {k : Over i₀} (_ : k ⟶ j),
      Scheme.IsSeparated ((D.map k.hom ⁻¹ᵁ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).toScheme) := by
    intro V
    have hVaff : IsAffine (V : S.Opens).toScheme := V.2
    have hWc : IsCompact ((t.app i₀ ⁻¹ᵁ (V : S.Opens) : (D.obj i₀).Opens) : Set (D.obj i₀)) :=
      QuasiCompact.isCompact_preimage _ (V : S.Opens).2 V.2.isCompact
    have : ∀ j : Over i₀,
        CompactSpace ((opensDiagram D i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).obj j) := fun j ↦
      isCompact_iff_compactSpace.mp
        (QuasiCompact.isCompact_preimage _ (t.app i₀ ⁻¹ᵁ (V : S.Opens)).2 hWc)
    have : ∀ j : Over i₀,
        QuasiSeparatedSpace ((opensDiagram D i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).obj j) := fun j ↦
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
    have : Scheme.IsSeparated (opensCone D c i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens))).pt := by
      constructor
      have he : terminal.from ((f ⁻¹ᵁ (V : S.Opens)).toScheme)
          = (f ∣_ (V : S.Opens)) ≫ terminal.from _ := Subsingleton.elim _ _
      change IsSeparated (terminal.from ((f ⁻¹ᵁ (V : S.Opens)).toScheme))
      rw [he]
      infer_instance
    exact Scheme.exists_isSeparated_of_isLimit
      (isLimitOpensCone D c hc i₀ (t.app i₀ ⁻¹ᵁ (V : S.Opens)))
  choose jj hjj using hstage
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.image jj s)
  refine ⟨jstar.left, ?_⟩
  intro i g
  set k : Over i₀ := Over.mk (g ≫ jstar.hom) with hk
  have gk : k ⟶ jstar := Over.homMk g
  have hnat : D.map k.hom ≫ t.app i₀ = t.app i := by
    have hn := t.naturality k.hom
    simp only [Functor.const_obj_map] at hn
    exact hn
  set U : S.Opens := ⨆ V ∈ s, (V : S.Opens) with hU
  have hrange : Set.range ⇑(t.app i).base ⊆ Set.range ⇑U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro x ⟨y, rfl⟩
    have : (t.app i).base y = (t.app i₀).base ((D.map k.hom).base y) := by
      rw [← hnat]
      rfl
    rw [this]
    have hmem := hs (Set.mem_range_self ((D.map k.hom).base y))
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨V, hVs, hV⟩ := hmem
    exact hU ▸ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨V, TopologicalSpace.Opens.mem_iSup.mpr ⟨hVs, hV⟩⟩
  set lift := IsOpenImmersion.lift U.ι (t.app i) hrange with hlift
  have hfac : lift ≫ U.ι = t.app i := IsOpenImmersion.lift_fac _ _ _
  rw [← hfac]
  have hsep : IsSeparated lift := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top
      (fun V : {V // V ∈ s} ↦ U.ι ⁻¹ᵁ (V.1 : S.Opens)) ?_ ?_
    · rw [← Scheme.Opens.ι_preimage_self U, hU, ← Scheme.Hom.preimage_iSup]
      congr 1
      rw [iSup_subtype]
    · intro V
      obtain ⟨m⟩ := hjstar (Finset.mem_image_of_mem jj V.2)
      have h2 := hjj V.1 (gk ≫ m)
      have h1 : lift ⁻¹ᵁ (U.ι ⁻¹ᵁ (V.1 : S.Opens)) = D.map k.hom ⁻¹ᵁ (t.app i₀ ⁻¹ᵁ (V.1 : S.Opens))
          := by rw [← Scheme.Hom.comp_preimage, hfac, ← hnat, Scheme.Hom.comp_preimage]
      have : Scheme.IsSeparated ((lift ⁻¹ᵁ (U.ι ⁻¹ᵁ (V.1 : S.Opens))).toScheme) := by
        rw [h1]; exact h2
      infer_instance
  infer_instance

end SeparatedDescent

end AlgebraicGeometry
