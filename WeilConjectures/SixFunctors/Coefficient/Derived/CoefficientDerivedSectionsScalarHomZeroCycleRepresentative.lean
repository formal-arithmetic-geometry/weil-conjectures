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

/-- The scalar transpose formula for one explicit zero-cycle representative.
Source: Stacks 03CZ, 079P and 08JA.
Proof: apply the finite tensor comparison square to the fixed Hom-complex
representative, use the uncurrying models to identify evaluation with the scalar
extension transpose, and then use the ordinary scalar-section formula. The
normalized zero-cycle equivalences turn the resulting chain-map equality into the
displayed derived-category equality.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-cycle-representative)
-/
theorem coefficientDerivedSectionsScalarHomZero_cycle_representative
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (N : CochainComplex (scalarReductionSource l E W) ℤ)
    (eN : DerivedCategory.Q.obj N ≅
      (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))
    (z : (coefficientHomSectionComplex.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W) P N).cycles 0)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op (DerivedCategory.Q.obj P),
          (coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M))))
    (hx :
      (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralGlobalHom l E W).map
            (Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj P))) eN.hom))
        (coefficientHomZeroClass.{u, t + 1, t, max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) P N z) = x) :
    coefficientFiniteHomEquiv l E W n _ _
        (coefficientDerivedSectionsScalarHomZeroMap l E W R D n
          (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M) x) =
      ((coefficientFiniteAdjunction l E W n).homEquiv
        (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj M)).symm
        (coefficientIntegralHomEquiv l E W (DerivedCategory.Q.obj P)
          ((coefficientFiniteDerivedRestriction l E W n).obj (DerivedCategory.Q.obj M)) x) := by
  sorry

end WeilConjectures
