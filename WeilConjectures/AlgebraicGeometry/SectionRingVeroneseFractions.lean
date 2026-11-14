/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionsCore
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionsFormula

/-! # Homogeneous section-ring fractions and Veronese section fractions

Source: Stacks Project, Properties, Tag 0B5L,
Lemma 01PW(2), and the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Homogeneous localization of the section ring at a section of degree `d` is the
additive presentation of fractions for the invertible module `L.tensorPow d`.
Source: Stacks Project, Properties, Tag 0B5L, Lemma 01PW(2) and Lemma 01Q1. -/
theorem exists_sectionRing_veronese_fraction_equiv
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    ∃ e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
        SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) =
        sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
          ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
            L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d))) := by
  let e := sectionRingVeroneseFractionEquiv X L d s
  exact ⟨e, sectionRing_veronese_fraction_formula X L d s e rfl⟩

end AlgebraicGeometry.Scheme.Modules
