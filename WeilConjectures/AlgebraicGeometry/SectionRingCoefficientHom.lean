/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientData

/-! # Coefficients in a homogeneous localization of a section ring

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

universe v
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- A section generating its tensor power on an open defines the coefficient ring map. -/
theorem exists_sectionRing_coefficient_hom
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        ρ (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d)) := by
  obtain ⟨c, hc0, hc1, hcadd, hcmul, hcoef⟩ :=
    exists_sectionRing_coefficient_data X L d s hd U hs
  let ρ : HomogeneousLocalization.Away (sectionRingGrade L) s.val →+* Γ(X, U) :=
    { toFun := c
      map_one' := hc1
      map_mul' := hcmul
      map_zero' := hc0
      map_add' := hcadd }
  exact ⟨ρ, hcoef⟩

end AlgebraicGeometry.Scheme.Modules
