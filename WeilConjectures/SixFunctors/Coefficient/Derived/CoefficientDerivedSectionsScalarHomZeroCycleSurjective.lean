/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentativeData

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Every H-zero class has a cycle representative after transporting the target
through a chosen quotient-image isomorphism.
Source: Stacks 08JA and the fixed K-injective Hom-complex construction.
Proof: since `eN.hom` is an isomorphism, the map induced on H-zero of the integral
global Hom in the second variable is bijective, so `x` is the image of a unique class
`y` in H-zero of the global Hom from `Q(P)` to `Q(N)`. The class map
`coefficientHomZeroClass` of the fixed Hom-section complex is the homology projection
of zero cycles (an epimorphism) followed by the isomorphism of the universal sections
comparison with the fixed K-injective replacement of `N`, as in the proof of
`coefficientHomZeroEquiv_exists`; hence `y` is the class of a zero cycle `z`, and the
image of that class is `x`. No hypothesis on `P` is needed.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-cycle-surjective)
-/
theorem coefficientDerivedSectionsScalarHomZero_cycle_surjective
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (n : ℕ)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (N : CochainComplex (scalarReductionSource l E W) ℤ)
    (eN : DerivedCategory.Q.obj N ≅
      (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op (DerivedCategory.Q.obj P),
          (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)))) :
    ∃ z : (coefficientHomSectionComplex.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N).cycles 0,
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralGlobalHom l E W).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom))
        (coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P N z) = x := by
  sorry

end WeilConjectures
