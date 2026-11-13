/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.SectionRingSingleQuotientChart
import WeilConjectures.AlgebraicGeometry.SectionRingQuotientChartOverlap

/-! # Compatible local quotient morphisms for the section ring

Source: Stacks Project, Properties, Tag 01PZ; Constructions, Tags 01N8 and 01NK.
-/

@[expose] public section

universe v w
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Local quotient morphisms on nonvanishing opens agree on overlaps. Their fraction
identities are equations of sections on the ambient image of each local chart
preimage (Stacks, Tags 01PZ, 01N8 and 01NK). -/
theorem exists_sectionRing_compatible_quotient_charts
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (I : Type w) (d : I → ℕ) (s : ∀ i, sectionRingGrade L (d i))
    (hd : ∀ i, 0 < d i) (U : I → X.Opens)
    (hU : ∀ i, (U i : Set X) =
      nonvanishingLocus (L.tensorPow (d i)) ((s i).val (d i))) :
    ∃ g : ∀ i, (U i).toScheme ⟶ Proj (sectionRingGrade L),
      (∀ i j, X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i) ≫ g i =
        X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j) ≫ g j) ∧
      ∀ i (e : ℕ) (_he : 0 < e) (t : sectionRingGrade L e)
        (n : ℕ) (ξ : sectionRingGrade L (n • e)),
        (show Γ(X, (U i).ι ''ᵁ (g i ⁻¹ᵁ
            Proj.basicOpen (sectionRingGrade L) t.val)) from
          (g i).app (Proj.basicOpen (sectionRingGrade L) t.val)
          (Proj.awayToSection (sectionRingGrade L) t.val
            (HomogeneousLocalization.Away.mk (sectionRingGrade L) t.property n
              ξ.val ξ.property))) •
          (L.tensorPow (n • e)).presheaf.map (homOfLE
            (le_top : (U i).ι ''ᵁ (g i ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
              ⊤)).op ((t.val ^ n) (n • e)) =
        (L.tensorPow (n • e)).presheaf.map (homOfLE
          (le_top : (U i).ι ''ᵁ (g i ⁻¹ᵁ Proj.basicOpen (sectionRingGrade L) t.val) ≤
            ⊤)).op (ξ.val (n • e)) := by
  classical
  have hchart (i : I) :=
    exists_sectionRing_single_quotient_chart X L (d i) (s i) (hd i) (U i) (hU i)
  choose g hg using hchart
  refine ⟨g, ?_, hg⟩
  intro i j
  exact sectionRing_quotient_charts_overlap X L (d i) (d j) (s i) (s j)
    (hd i) (hd j) (U i) (U j) (hU i) (hU j) (g i) (g j) (hg i) (hg j)

end AlgebraicGeometry.Scheme.Modules
