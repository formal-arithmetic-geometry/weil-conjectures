/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSystemEvaluationData

/-! The representative-input transpose step for H-zero scalar normalization.
Source: Stacks 03CZ, 079P and 08JA.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-representative)
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

/--
For a K-flat representative of the scalar input and an arbitrary complex
representing the finite input, the normalized representative transpose gives the
H-zero scalar Hom identity.  The remaining transport from arbitrary derived
objects is separate from this representative calculation.

Source: Stacks 03CZ, 079P and 08JA.  Choose the fixed K-injective replacement of
the finite complex, apply the tensor-Hom uncurrying equation from the coefficient
finite tensor normalization, and evaluate the resulting zero cycle using the
fixed representative Hom equivalences.  The ordinary scalar-section formula
identifies the transpose with the finite scalar adjunction.  This theorem is
strictly below the derived-object statement because its first input is a chosen
K-flat complex and both derived inputs are fixed quotient images.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero-representative)
-/
theorem coefficientDerivedSectionsScalarHomZero_representative
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W)
    (n : ℕ)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := Scheme.ProEt.topology W)
      (R := completedIntegralCommRingSheafUnrestricted l E W) P)
    (M : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (P' : DerivedCategory (scalarReductionSource l E W))
    (M' : normalizedDVRDerived l E W n)
    (hP' : P' = DerivedCategory.Q.obj P)
    (hM' : M' = DerivedCategory.Q.obj M) :
    ∀ (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj (op P',
        (coefficientFiniteDerivedRestriction l E W n).obj M'))),
      coefficientFiniteHomEquiv l E W n _ _
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
            ((coefficientIntegralSections l E W).map
                (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
                  (coefficientFiniteDerivedExtension l E W n)
                  (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P' M') ≫
              (D.scalarSections n).hom.app
                ((coefficientFiniteInternalHom l E W n).obj
                  (op ((coefficientFiniteDerivedExtension l E W n).obj P'), M'))) x) =
        ((coefficientFiniteAdjunction l E W n).homEquiv P' M').symm
          (coefficientIntegralHomEquiv l E W P' _ x) := by
  sorry

end WeilConjectures
