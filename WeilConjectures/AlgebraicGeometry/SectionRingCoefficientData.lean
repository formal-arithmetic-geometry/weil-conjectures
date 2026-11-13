/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientNumerator
import WeilConjectures.AlgebraicGeometry.SectionRingCoefficientArithmetic
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- Coefficient data on a homogeneous localization: if `s` restricts to a free generator over
`U`, there is a ring-hom-like map `c` from the degree-zero localization at `s` to `Γ(X, U)`
with `c (ξ / s ^ n) • s ^ n = ξ` on `U`. -/
theorem exists_sectionRing_coefficient_data
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U),
      c 0 = 0 ∧ c 1 = 1 ∧
      (∀ a b, c (a + b) = c a + c b) ∧
      (∀ a b, c (a * b) = c a * c b) ∧
      (∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d))) := by
  obtain ⟨c, hn⟩ := exists_sectionRing_coefficient_numerator X L d s hd U hs
  obtain ⟨h0, h1, ha, hm⟩ := sectionRing_coefficient_arithmetic_of_numerator X L d s hd U hs c hn
  exact ⟨c, h0, h1, ha, hm, hn⟩
end AlgebraicGeometry.Scheme.Modules
