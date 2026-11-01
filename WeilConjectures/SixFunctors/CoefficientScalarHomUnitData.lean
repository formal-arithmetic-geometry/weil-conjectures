/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.SixFunctors.CoefficientHomZeroUnitEvaluation
import WeilConjectures.CategoryTheory.RepresentedSectionsScalarUnit

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

def coefficientScalarHomSectionsIso
    (D : CoefficientDerivedSystemScalarCoherence l E W) (n : ℕ) :
    coefficientFiniteDerivedRestriction l E W n ⋙
        ringedSiteZerothHypercohomologyOfUniverses.{t + 1, t, u,
          max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W) ≅
      ringedSiteZerothHypercohomologyOfUniverses.{t + 1, t, u,
        max (t + 2) (u + 1)} (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) :=
  Functor.isoWhiskerRight (D.scalarSections n)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0)

end WeilConjectures
