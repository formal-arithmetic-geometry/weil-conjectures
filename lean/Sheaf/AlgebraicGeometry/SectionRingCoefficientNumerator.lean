module
public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- Existence of a coefficient function satisfying the numerator equation.
The function is obtained by the local quotient construction of Stacks Tags 01N8 and 01NK.
(blueprint: lem-sc-section-ring-coefficient-data-numerator)

Write e_n for the restriction of the degree-n*d component of s^n. The section-ring
product is the tensor product transported by tensorPowAddIso. Restriction preserves
this product, so induction from hs, the unit generator, and IsFreeGenerator.tmulSection
shows that each e_n is a free generator. For a numerator a of degree n*d, let r_n(a)
be the unique scalar with r_n(a) • e_n equal to its restriction to U.
If a/s^n = b/s^m, localization equality supplies k with
s^k * (a*s^m - b*s^n) = 0. Restrict and use bilinearity to get
(r_n(a) - r_m(b)) • e_(k+n+m) = 0. Injectivity of scalar multiplication
by that free generator gives r_n(a) = r_m(b). Every fraction has such a
representative by Away.mk_surjective, so these coefficients descend to a function.
Its numerator equation is the defining equation of r_n(a). This also works on the
empty open: the scalar ring and section modules there are trivial. -/
theorem exists_sectionRing_coefficient_numerator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d))) :
    ∃ c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U),
      ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
        c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
            ξ.val ξ.property) •
          (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            ((s.val ^ n) (n • d)) =
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          (ξ.val (n • d)) := by sorry
end AlgebraicGeometry.Scheme.Modules
