/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedCoefficientSquare

import all WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFiniteRawScalarComparison

/-! # The raw ambient comparison is the completion map

The quotient-normalized coefficient isomorphisms intertwine the completed scalar map of the
finite coefficient stages with the completed coefficient map. The ambient comparison of a
completion-integral comparison is the specified completion map, transported along the tensor
comparison through this coefficient square.

## Main statements

* `AlgebraicGeometry.Scheme.purCoefficientIso_hom_comp_completedCoefficientMap`: the coefficient
  square of an inclusion of finite coefficient fields.
* `WeilConjectures.AdicFiniteRealization.FiniteCondensedData.rawComparison_hom_app`: the ambient
  comparison of the raw integral data is the transported completion map.

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Lemma 6.8.2 and
  Proposition 6.8.14(2)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe w u
open CategoryTheory
open WeilConjectures.LocallyFiniteAdicRealization

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] (T : Scheme.{u})

/-- The quotient-normalized coefficient isomorphisms intertwine the completed scalar map of the
finite coefficient stages with the completed coefficient map of the field inclusion. -/
theorem purCoefficientIso_hom_comp_completedCoefficientMap
    {E L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ L) :
    (WeilConjectures.purCoefficientIso l (pbcFiniteField.{u} l Ω E) T).hom ≫
        WeilConjectures.completedCoefficientMap l (pbcFiniteField.{u} l Ω E)
          (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) T =
      pbcCompletedScalarMap l Ω T h ≫
        (WeilConjectures.purCoefficientIso l (pbcFiniteField.{u} l Ω L) T).hom := by
  rw [← WeilConjectures.scalarMap_eq_completed, WeilConjectures.coefficientScalar_square,
    rawScalar_coefficientMap]

end AlgebraicGeometry.Scheme

namespace WeilConjectures.AdicFiniteRealization

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicallyClosedCoefficients

/-- The completed scalar map of finite coefficient stages, between the completed coefficients
of the coefficient fields of the fixed closure. -/
def coefficientCompletedScalarMap (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) E)) ⟶
      pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) L)) :=
  pbcCompletedScalarMap l (PadicAlgCl l) X h

/-- The completed coefficient square of an inclusion of coefficient fields of the fixed
closure. -/
theorem purCoefficientIso_hom_comp_completedCoefficientMap_index (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X).hom ≫
        completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X =
      coefficientCompletedScalarMap l X h ≫
        (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X).hom :=
  purCoefficientIso_hom_comp_completedCoefficientMap l (PadicAlgCl l) X h

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}} [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The ambient comparison of the raw integral data is the specified completion map, transported
along the tensor comparison through the coefficient square. -/
theorem FiniteCondensedData.rawComparison_hom_app (A : FiniteCondensedData l X)
    {E L : Index l (PadicAlgCl l)} (h : E ≤ L)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) X) :
    (A.raw.integral.comparison h).hom.app K ≍
      (tensorThroughCoefficientSquare X (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X)
          (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X)
          (coefficientCompletedScalarMap l X h)
          (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h) X)
          (purCoefficientIso_hom_comp_completedCoefficientMap_index l X h)).inv.app
          ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K) ≫
        (pbcDerivedRestrict (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) L) X).hom).map
          ((completedTensorComparison l X (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L) (coefficientInclusion l (PadicAlgCl l) E L h)).app
              ((sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι.obj K)) := by
  sorry

end WeilConjectures.AdicFiniteRealization

namespace WeilConjectures.LocallyFiniteAdicRealization

open AlgebraicGeometry AlgebraicGeometry.Scheme AdicFiniteRealization
open scoped Obj
open AlgebraicallyClosedCoefficients (Index Coefficient)

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)] [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]

/-- The continuous integral realization map, with source the completed coefficients of the
coefficient field of the fixed closure. -/
def realizationCoefficientMap (A : FiniteCondensedData l X) (E : Index l (PadicAlgCl l)) :
    pbcAdicCompletion X (pbcIntegralDatum l (Coefficient.{u} l (PadicAlgCl l) E)) ⟶
      rationalCoefficientSheaf l X (pbcFiniteField.{u} l (PadicAlgCl l) E) :=
  (A.realization E).integralIso.hom ≫ (A.realization E).inclusion

/-- The coefficient square of the continuous realization and the coefficient presentation. -/
theorem finiteOrdinaryCoefficientSquare (A : FiniteCondensedData l X)
    (C : CoefficientSystem l X) (E : Index l (PadicAlgCl l)) :
    letI := C.commutative
    letI := sectionRingMap_isIso X (condensedNativeMap l X)
    (purCoefficientIso l (Coefficient.{u} l (PadicAlgCl l) E) X).hom ≫
        (C.coefficient E).integralMap l X =
      (realizationCoefficientMap l X A E ≫ A.closure.leg E) ≫
        (asIso (ProEtale.CondensedRing.sectionRingMap X (condensedNativeMap l X))).hom := by
  dsimp only [asIso_hom, realizationCoefficientMap]
  simp only [Category.assoc]
  exact finiteCondensedIntegralCoefficientSquare l X A E (C.coefficient E)

/-- The completed scalar square of the continuous realizations. -/
theorem coefficientCompletedScalarMap_comp_realizationCoefficientMap
    (A : FiniteCondensedData l X) {E L : Index l (PadicAlgCl l)} (h : E ≤ L) :
    coefficientCompletedScalarMap l X h ≫ realizationCoefficientMap l X A L =
      realizationCoefficientMap l X A E ≫ (A.scalar.coefficient h).coefficient :=
  A.scalar.completed_square h

end WeilConjectures.LocallyFiniteAdicRealization
