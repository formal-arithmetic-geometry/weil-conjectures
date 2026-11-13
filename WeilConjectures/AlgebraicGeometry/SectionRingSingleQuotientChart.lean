/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientHom
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartTransfer

/-! # A single quotient chart for an invertible section ring

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A single positive-degree section gives a quotient morphism on its nonvanishing open.
No compatibility with a second morphism is asserted. -/
theorem exists_sectionRing_single_quotient_chart
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hU : (U : Set X) = nonvanishingLocus (L.tensorPow d) (s.val d)) :
    ∃ g : U.toScheme ⟶ Proj (sectionRingGrade L),
      ∀ (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
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
            ⊤)).op (ξ.val (n • e)) := by
  obtain ⟨V, hV, _, hcoeff⟩ :=
    nonvanishing_section_trivializes X (L.tensorPow d) (s.val d)
  have hVU : V = U := SetLike.coe_injective (hV.trans hU.symm)
  subst V
  have hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)) := by
    intro W hW
    have hc := hcoeff W hW
    simp only [presheaf_map_map_apply]
    constructor
    · intro a b hab
      obtain ⟨c, _, huniq⟩ := hc (a • (L.tensorPow d).presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op (s.val d))
      exact (huniq a rfl).trans (huniq b hab).symm
    · intro t
      obtain ⟨a, ha, _⟩ := hc t
      exact ⟨a, ha.symm⟩
  obtain ⟨ρ, hρ⟩ := exists_sectionRing_coefficient_hom X L d s hd U hs
  let φ := CommRingCat.ofHom ρ ≫ U.topIso.inv
  let q := (ΓSpec.adjunction.homEquiv U.toScheme
    (.op (.of (HomogeneousLocalization.Away (sectionRingGrade L) s.val)))) φ.op
  have hq : (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
      (sectionRingGrade L) s.val))).inv ≫ q.appTop = φ :=
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv φ
  refine ⟨q ≫ Proj.awayι (sectionRingGrade L) s.val s.property hd, ?_⟩
  exact sectionRing_quotient_chart_transfer X L d s hd U hs ρ hρ q hq


end AlgebraicGeometry.Scheme.Modules
