/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.Section.SectionRingLocalizationBijective
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Affine charts of the canonical section-ring morphism

Source: Stacks Project, Properties, Tags 01PZ and 01Q1, with the chart formula of
Constructions Tag 01N8.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical section-ring morphism identifies any affine nonvanishing chart when `L`
is ample. Here `X_s` is `nonvanishingLocus (L.tensorPow d) (s.val d)`.
Source: Stacks Project, Properties, Tags 01PZ and 01Q1. -/
theorem exists_sectionRing_proj_affine_charts (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible]
    (hcover : ∀ x : X, ∃ (d : ℕ) (s : sectionRingGrade L d),
      0 < d ∧ x ∈ nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ f : X ⟶ Proj (sectionRingGrade L),
      ∀ (d : ℕ) (_hd : 0 < d) (s : sectionRingGrade L d),
        (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val : Set X) =
          nonvanishingLocus (L.tensorPow d) (s.val d) ∧
        (∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
          (f.app (Proj.basicOpen (sectionRingGrade L) s.val)
            (Proj.awayToSection (sectionRingGrade L) s.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
              ((s.val ^ n) (n • d)) =
          (L.tensorPow (n • d)).presheaf.map (homOfLE
              (le_top : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val ≤ ⊤)).op
            (ξ.val (n • d))) ∧
        (IsAmple X L → ∀ U : X.Opens,
          (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d) → IsAffineOpen U →
          IsIso (f ∣_ Proj.basicOpen (sectionRingGrade L) s.val)) := by
  obtain ⟨f, hf⟩ := exists_sectionRing_proj_morphism X L hcover
  refine ⟨f, ?_⟩
  intro d hd s
  obtain ⟨hpre, hformula⟩ := hf d hd s
  refine ⟨hpre, hformula, ?_⟩
  intro hL U hU hAffine
  have : CompactSpace X := hL.1
  have : X.IsSeparated := isSeparated_of_isAmple X L hL
  have hsource : IsAffineOpen (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val) := by
    have heq : f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val = U := by
      apply SetLike.coe_injective
      exact hpre.trans hU.symm
    exact heq.symm ▸ hAffine
  have hbij := sectionRing_localization_bijective X L d hd s
    (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val) hpre
    (Proj.awayToSection (sectionRingGrade L) s.val ≫
      f.app (Proj.basicOpen (sectionRingGrade L) s.val)) hformula
  have haway : IsIso (Proj.awayToSection (sectionRingGrade L) s.val) := by
    rw [← Proj.basicOpenIsoAway_hom (sectionRingGrade L) s.val s.property hd]
    infer_instance
  have hcomp : IsIso (Proj.awayToSection (sectionRingGrade L) s.val ≫
      f.app (Proj.basicOpen (sectionRingGrade L) s.val)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have happ : IsIso (f.app (Proj.basicOpen (sectionRingGrade L) s.val)) := by
    exact (isIso_comp_left_iff _ _).mp hcomp
  have : IsAffine (f ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) s.val).toScheme := hsource
  have : IsAffine (Proj.basicOpen (sectionRingGrade L) s.val).toScheme :=
    Proj.isAffineOpen_basicOpen (sectionRingGrade L) s.val s.property hd
  have : IsIso (f ∣_ Proj.basicOpen (sectionRingGrade L) s.val).appTop := by
    rw [morphismRestrict_appTop]
    have happ' (V : (Proj (sectionRingGrade L)).Opens)
        (hV : V = Proj.basicOpen (sectionRingGrade L) s.val) : IsIso (f.app V) := by
      subst V
      exact happ
    have := happ' _ (Scheme.Opens.ι_image_top _)
    infer_instance
  exact (HasAffineProperty.iff_of_isAffine
    (P := MorphismProperty.isomorphisms Scheme)).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
