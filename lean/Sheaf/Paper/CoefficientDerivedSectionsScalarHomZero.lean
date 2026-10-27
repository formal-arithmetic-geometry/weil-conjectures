/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! The H-zero scalar normalization extracted from the coefficient-sections package.
(blueprint: lem-coef-derived-sections-scalar-hom-zero)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The H-zero finite scalar comparison is the normalized adjunction transpose.
Source: Stacks 03CZ, 079P and 08JA.
Choose K-flat and K-injective representatives, identify the enriched map with the
ordinary tensor-Hom transpose, and transport degree-zero cocycles through the fixed
representative evaluation equivalences.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero) -/
theorem coefficientDerivedSectionsScalarHomZero
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W) :
    ∀ (n : ℕ)
    (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientFiniteDerivedRestriction l E W n).obj M))),
      coefficientFiniteHomEquiv l E W n _ _
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
            ((coefficientIntegralSections l E W).map
                (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
                  (coefficientFiniteDerivedExtension l E W n)
                  (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P M) ≫
              (D.scalarSections n).hom.app
                ((coefficientFiniteInternalHom l E W n).obj
                  (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) x) =
        ((coefficientFiniteAdjunction l E W n).homEquiv P M).symm
          (coefficientIntegralHomEquiv l E W P _ x) := by
  sorry

end WeilConjectures
