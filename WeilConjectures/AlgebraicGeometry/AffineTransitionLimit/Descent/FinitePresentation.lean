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
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Gluing
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
import all WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone

/-!
# Descending a scheme of finite presentation to a finite stage

A scheme of finite presentation over a cofiltered limit of quasi-compact quasi-separated schemes
with affine transition maps is the base change of a scheme of finite presentation over one of
the stages (`AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation`, Stacks Project
Tag 01ZM).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent
section Descent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- (Implementation) **Descent to a finite stage for a finite union of affine opens**, each of
which lies over an affine open of the stage `i₀`. -/
lemma descendsToStage_finsetSup {X : Scheme.{u}} [QuasiSeparatedSpace X] {i₀ : I} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] (s : Finset X.Opens)
    (hs : ∀ W ∈ s, IsAffineOpen W ∧
      ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c ((s.sup id : X.Opens).ι ≫ g) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sup_empty]
      exact DescendsToStage.of_isAffineOpen hc g (isAffineOpen_bot X)
        (isAffineOpen_bot (D.obj i₀)) bot_le
  | insert a s ha ih =>
      obtain ⟨haff, Va, hVa, hale⟩ := hs a (Finset.mem_insert_self a s)
      have hsaff : ∀ W ∈ s, IsAffineOpen W ∧
          ∃ V : (D.obj i₀).Opens, IsAffineOpen V ∧ W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V :=
        fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      rw [Finset.sup_insert, id]
      set Z : X.Opens := a ⊔ s.sup id with hZ
      have : QuasiSeparatedSpace Z.toScheme :=
        QuasiSeparatedSpace.of_isOpenEmbedding Z.ι.isOpenEmbedding
      set U : Z.toScheme.Opens := Z.ι ⁻¹ᵁ (s.sup id) with hUdef
      set V : Z.toScheme.Opens := Z.ι ⁻¹ᵁ a with hVdef
      have hUV : U ⊔ V = ⊤ := by
        rw [hUdef, hVdef, ← Scheme.Hom.preimage_sup, sup_comm, ← hZ,
          Scheme.Opens.ι_preimage_self]
      -- the intersection is quasi-compact
      have hsc : IsCompact ((s.sup id : X.Opens) : Set X) :=
        isCompact_finset_sup s fun W hW ↦ (hsaff W hW).1.isCompact
      have hinfc : IsCompact (((s.sup id ⊓ a : X.Opens)) : Set X) := by
        rw [TopologicalSpace.Opens.coe_inf]
        exact QuasiSeparatedSpace.inter_isCompact _ _ (s.sup id).2 hsc a.2 haff.isCompact
      have hUVc : IsCompact ((U ⊓ V : Z.toScheme.Opens) : Set Z.toScheme) := by
        have he : (U ⊓ V : Z.toScheme.Opens) = Z.ι ⁻¹ᵁ (s.sup id ⊓ a) := by
          rw [hUdef, hVdef, Scheme.Hom.preimage_inf]
        rw [he]
        refine Z.ι.isOpenEmbedding.isInducing.isCompact_preimage' hinfc ?_
        rw [Scheme.Opens.range_ι]
        exact le_trans inf_le_left le_sup_right
      refine DescendsToStage.of_sup_eq_top hc (Z.ι ≫ g) U V hUV hUVc ?_ ?_
      · -- the first open is the union over `s`, which descends by the induction hypothesis
        have hrange : Set.range (U.ι ≫ Z.ι) = Set.range (s.sup id : X.Opens).ι := by
          rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
          congr 1
          simp only [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι, hUdef,
            Scheme.Hom.image_preimage_eq_opensRange_inf, hZ]
          exact inf_eq_right.mpr (le_sup_right : (s.sup id : X.Opens) ≤ a ⊔ s.sup id)
        have := DescendsToStage.comp_iso
          (IsOpenImmersion.isoOfRangeEq (U.ι ≫ Z.ι) (s.sup id : X.Opens).ι hrange) (ih hsaff)
        rwa [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc] at this
      · -- the second open is affine and lies over an affine open of the stage `i₀`
        refine DescendsToStage.of_isAffineOpen hc (Z.ι ≫ g) ?_ hVa ?_
        · refine haff.preimage_of_isOpenImmersion Z.ι ?_
          rw [Scheme.Opens.opensRange_ι, hZ]
          exact le_sup_left
        · rw [Category.assoc, Scheme.Hom.comp_preimage]
          exact Z.ι.preimage_mono hale

set_option backward.isDefEq.respectTransparency false in
include hc in
/-- **Schemes of finite presentation over a cofiltered limit of quasi-compact quasi-separated
schemes descend to a finite stage** (Stacks Project Tag 01ZM). Let `{Dⱼ}` be a cofiltered
inverse system of quasi-compact quasi-separated schemes with affine transition maps and let
`X` be of finite presentation over `lim Dⱼ`. Then `X` is the base change of a scheme `Y` of
finite presentation over one of the `Dⱼ`.

The affine case is
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`; the
general case follows by induction over a finite cover of `X` by affine opens each of which
lies over an affine open of a fixed stage, gluing the descended charts over a common stage.
(Blueprint: `lemma:nagata-finite-presentation-descends`.) -/
@[stacks 01ZM]
theorem Scheme.exists_isPullback_of_finitePresentation [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] :
    ∃ (i : I) (Y : Scheme.{u}) (p : Y ⟶ D.obj i) (_ : LocallyOfFinitePresentation p)
      (_ : QuasiCompact p) (_ : QuasiSeparated p) (h : X ⟶ Y),
      IsPullback h g p (c.π.app i) := by
  classical
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  have := isAffineHom_π_app _ _ hc
  have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (c.π.app i₀)
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i₀)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated g
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_affineOpens_le_preimage (g ≫ c.π.app i₀)).exists_finite_of_isCompact
      (U := ⊤) (by simpa using isCompact_univ)
  have H := descendsToStage_finsetSup hc (i₀ := i₀) g hUsfin.toFinset
    (fun W hW ↦ hUsB (hUsfin.mem_toFinset.mp hW))
  rw [Finset.sup_id_eq_sSup, hUsfin.coe_toFinset, ← hUs] at H
  replace H := DescendsToStage.comp_iso X.topIso.symm H
  rw [Iso.symm_hom, ← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at H
  obtain ⟨i, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  exact ⟨i, Y, p, hp, inferInstance, inferInstance, h, hsq⟩

end Descent

end FinitePresentationDescent

end AlgebraicGeometry
