/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlapPointwise

/-! # Underlying maps of section-ring quotient charts

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying continuous maps of the restricted quotient charts agree. -/
theorem sectionRing_overlap_base_map
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d e : ℕ) (s : sectionRingGrade L d) (t : sectionRingGrade L e)
    (hd : 0 < d) (he : 0 < e) (U V : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d))
    (hV : (V : Set X) = nonvanishingLocus (L.tensorPow e) (t.val e))
    (g : U.toScheme ⟶ Proj (sectionRingGrade L))
    (h : V.toScheme ⟶ Proj (sectionRingGrade L))
    (hg : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, U.ι ''ᵁ (g ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            g.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : U.ι ''ᵁ (g ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e)))
    (hh : ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
          (n : ℕ) (ξ : sectionRingGrade L (n • e)),
          (show Γ(X, V.ι ''ᵁ (h ⁻¹ᵁ
              Proj.basicOpen (sectionRingGrade L) t.val)) from
            h.app (Proj.basicOpen (sectionRingGrade L) t.val)
            (Proj.awayToSection (sectionRingGrade L) t.val
              (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
                ξ.val ξ.property))) •
            (L.tensorPow (n • e)).presheaf.map (homOfLE
              (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
                ⊤)).op ((t.val ^ n) (n • e)) =
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : V.ι ''ᵁ (h ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op (ξ.val (n • e))) :
    (X.homOfLE (inf_le_left : U ⊓ V ≤ U) ≫ g).base =
      (X.homOfLE (inf_le_right : U ⊓ V ≤ V) ≫ h).base := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact sectionRing_overlap_base_map_pointwise X L d e s t hd he U V hU hV g h hg hh x

end AlgebraicGeometry.Scheme.Modules
