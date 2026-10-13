module

public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Sheaf.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- Formula for the Veronese fraction equivalence on homogeneous generators.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-formula)
Under the tensor-power identification, the fraction represented by a degree `n • d`
section is the corresponding section-fraction generator.
-/
theorem sectionRing_veronese_fraction_formula
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d)
    (e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
    (he : e = Classical.choice (sectionRing_veronese_fraction_core X L d s)) :
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property) =
      sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
        ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
          L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
