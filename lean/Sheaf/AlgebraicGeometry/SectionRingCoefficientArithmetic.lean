module
public import Sheaf.AlgebraicGeometry.InvertibleSectionRing
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- The numerator equation uniquely determines the coefficient function and its ring laws.
This is the uniqueness and arithmetic part of the quotient construction (Stacks Tags 01N8, 01NK).
(blueprint: lem-sc-section-ring-coefficient-data-arithmetic)

As in the numerator construction, restriction of s^n is a free generator e_n:
induct using the unit generator, hs, tensor products and tensorPowAddIso.
Apply hn to the degree-zero numerators zero and one, both with denominator s^0.
Scalar multiplication by e_0 is injective, so c(0)=0 and c(1)=1.
For arbitrary fractions use Away.mk_surjective to write a/s^n and b/s^m.
Their sum has numerator a*s^m+b*s^n and denominator s^(n+m).
Restrict this identity and apply hn to both summands. Bilinearity gives
(c(a/s^n)+c(b/s^m)) • e_(n+m) as its numerator section; hn for the sum
and injectivity for e_(n+m) prove additivity. The product has numerator a*b
and the same denominator s^(n+m). Tensor bilinearity gives
(c(a/s^n)*c(b/s^m)) • e_(n+m); the same injectivity proves multiplicativity.
All degree transports are the tensorPowAddIso transports in sectionRingGMul,
and restriction commutes with them by naturality. No cancellation in the
global section ring is assumed. -/
theorem sectionRing_coefficient_arithmetic_of_numerator
    (X : Scheme.{v}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) (hd : 0 < d) (U : X.Opens)
    (hs : IsFreeGenerator ((L.tensorPow d).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (s.val d)))
    (c : HomogeneousLocalization.Away (sectionRingGrade L) s.val → Γ(X, U))
    (hn : ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      c (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
          ξ.val ξ.property) •
        (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
          ((s.val ^ n) (n • d)) =
      (L.tensorPow (n • d)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (ξ.val (n • d))) :
    c 0 = 0 ∧ c 1 = 1 ∧ (∀ a b, c (a + b) = c a + c b) ∧
      (∀ a b, c (a * b) = c a * c b) := by sorry
end AlgebraicGeometry.Scheme.Modules
