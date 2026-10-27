/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.ConnectedConstantH0
public import Sheaf.Paper.ConstantWeilStructure
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.FrobeniusExchangeDegreeZero
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.IntegralPointTransportTowerRealization
import Sheaf.Paper.CanonicalCoefficientPullbackReduction
import Sheaf.Paper.BasicOperationsCoefficientReduction

/-! # Frobenius fixes the constant unit class

Source: blueprint main-20261015, cohomological finiteness, Proof Step 7
(blueprint: lem-pod-frobenius-fixes-unit-section).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (E : Padic.FiniteCoefficientFields c.l c.Qbar)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom] [ConnectedSpace (D.geometricFiber Y₀).left]

/-- The whole-system direct image used by the recorded Frobenius operator.
Source: blueprint cohomological finiteness, Proof Steps 5 and 7
(blueprint: lem-pod-frobenius-fixes-unit-section). -/
def frobeniusUnitIntegralImage :
    sfIntegralConstructibleCategory c.l E.val (Spec (.of D.k)) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  exact (FrobeniusExchange.directImageFunctor c.l E.val D.k
    (finiteFieldDatumPrimeUnit D c.l c.different) (D.geometricFiber Y₀).hom).obj
      (integralCohomologyCoefficient D c.l c.different E.val (D.geometricFiber Y₀).left)

/-- The actual finite evaluation of the whole-system direct image: apply the
reconstruction counit, the section-normalized direct-image evaluation mate, and the
specified input reduction identification. The exponent is n+1.
Source: blueprint cohomological finiteness, Proof Steps 5 and 7
(blueprint: lem-pod-frobenius-fixes-unit-section). -/
def frobeniusUnitFiniteComparison (n : ℕ) :=
  (((FrobeniusExchange.models c.l E.val).system (Spec (.of D.k))).reductionEvaluation n).inv.app
      (frobeniusUnitIntegralImage D c E Y₀).obj ≫
    (coefficientSequenceDerivedEvaluation c.l E.val (Spec (.of D.k)) n).map
      ((FrobeniusExchange.operationReduction c.l E.val
        (FrobeniusExchange.systemDirect c.l E.val (D.geometricFiber Y₀).hom)).app
          (integralCohomologyCoefficient D c.l c.different E.val
            (D.geometricFiber Y₀).left).obj) ≫
    (FrobeniusExchange.systemDirectEvaluation c.l E.val (D.geometricFiber Y₀).hom n).app
      ((FrobeniusExchange.reduction c.l E.val (D.geometricFiber Y₀).left).obj
        (integralCohomologyCoefficient D c.l c.different E.val
          (D.geometricFiber Y₀).left).obj) ≫
    (proEtaleConstantDerivedDirectImage (D.geometricFiber Y₀).hom
      (Padic.coefficientExtensionRing c.l E.val (n + 1))).map
        ((((FrobeniusExchange.models c.l E.val).system
          (D.geometricFiber Y₀).left).reductionEvaluation n).hom.app
            (integralCohomologyCoefficient D c.l c.different E.val
              (D.geometricFiber Y₀).left).obj)

/-- The canonical comparison is characterized by the actual Roos projections, before
rationalization, and then by the recorded point fibre and H⁰ functors.
Source: blueprint cohomological finiteness, Proof Steps 5 and 7
(blueprint: lem-pod-frobenius-fixes-unit-section). -/
def FrobeniusUnitH0ComparisonSpec (c₀ : Compactification Y₀.hom)
    (α : rationalOrdinaryCohomology D c.l c.different E.val (D.geometricFiber Y₀).left
        (rationalCohomologyCoefficient D c.l c.different E.val (D.geometricFiber Y₀).left) 0 ≅
      (DerivedCategory.coefficientFdCohomology E.val 0).obj
        ((frobeniusCohomologyRationalFunctor D c.l c.different E.val Y₀ c₀ false).obj
          (constantWeilRationalComplex c.l E.val D c.different Y₀).carrier)) : Prop :=
  ∃ β : integralImage D c.l c.different E.val (D.geometricFiber Y₀).left
        (integralCohomologyCoefficient D c.l c.different E.val (D.geometricFiber Y₀).left) ⟶
      frobeniusUnitIntegralImage D c E Y₀,
    (∀ n : ℕ,
      (scalarReductionDerivedExtension c.l E.val (Spec (.of D.k)) n).map β.hom ≫
          frobeniusUnitFiniteComparison D c E Y₀ n =
        sfDirectImageReductionComparison c.l E.val (D.geometricFiber Y₀).hom
          (connectedIntegralImage D c.l c.different E.val (D.geometricFiber Y₀).left) n) ∧
    α.hom = (DerivedCategory.coefficientFdCohomology E.val 0).map
      ((pointRationalFibre D c.l c.different E.val).map
        ((sfRationalConstructibleLocalization c.l E.val (Spec (.of D.k))).map β))

/-- There is a unique H⁰ comparison with the projection normalization above.
Source: blueprint cohomological finiteness, Proof Steps 5 and 7; the ordinary-cohomology
presentation identification implicit in the unit class
(blueprint: lem-pod-frobenius-fixes-unit-section).
Proof: whole-system direct-image evaluation and its reconstruction counit present the
image by the same finite-image tower as connectedIntegralImage, with the displayed
finite comparisons as its actual projections. Complete the identity square on the
product and 1-shift to an isomorphism of Roos triangles. The resulting β satisfies
the stated equations by the scalar extension/restriction adjunction. Rationalize,
apply the recorded point fibre and H⁰ to obtain α. Negative finite cohomology vanishes
for the regular coefficient sheaves in degree zero. The degree-zero Milnor sequence
therefore makes the finite projections jointly injective on integral H⁰. Hence all such
β induce the same integral H⁰ map. Exact scalar localization and the canonical tensor
comparison give the same rational H⁰ map, proving uniqueness of α, including its inverse.
No derived morphism is asserted to be determined by its individual finite reductions. -/
theorem frobeniusUnitH0Comparison_existsUnique (c₀ : Compactification Y₀.hom) :
    ∃! α, FrobeniusUnitH0ComparisonSpec D c E Y₀ c₀ α := by
  sorry

/-- Transport from the recorded constant H⁰ presentation to the recorded Frobenius
presentation, chosen only from its unique projection-normalized characterization.
Source: blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-frobenius-fixes-unit-section). -/
def frobeniusUnitH0Comparison (c₀ : Compactification Y₀.hom) :=
  (frobeniusUnitH0Comparison_existsUnique D c E Y₀ c₀).exists.choose

/-- The geometric Frobenius fixes the specified constant unit class.
Source: blueprint main-20261015, cohomological finiteness, Proof Step 7
(blueprint: lem-pod-frobenius-fixes-unit-section).
Proof dependencies: lem-weil-constant-coefficient-objects-constructible,
def-weil-frobenius-cohomology-transport, def-weil-frobenius-square-exchange,
def-weil-frobenius-point-transport, lem-pod-frobenius-exchange-degree-zero,
lem-weil-point-proetale-sections-exact, lem-sf-integral-direct-image-constructible,
def-weil-constant-weil-structure, lem-trf-integral-point-transport-tower-realization,
lem-pod-canonical-coefficient-pullback-reduction, lem-fix-operation-reduction,
lem-pod-connected-constant-h0, and def-weil-global-geometric-frobenius.
Proof: (1) For B_n=(A_{E,n})_Y, constructibility and integral-direct-image
constructibility place the finite images in the bounded constructible point category.
Unfold the transport as the specified point map followed by the unit-square-counit
exchange mate. The degree-zero exchange computation and exact point sections identify
this composite, after lambda_n, with restriction and colimit insertion of sections.
(2) The adjoint defining c_n sends every constant to that same constant; thus the finite
operator fixes 1, compatibly with quotient transitions.
(3) Apply integral-direct-image constructibility to the completed regular coefficient
object. The integral point-transport tower-realization theorem then identifies its
specified point map with the realization of these finite maps.
(4) The canonical coefficient pullback reduction theorem normalizes lambda_R and theta_R
on actual projections. Operation reduction preserves units, counits and the square mate,
so each projection P_n intertwines the integral operator with the finite operator.
(5) The connected-constant-H⁰ theorem makes P_n jointly injective and sends the integral
unit to every finite unit. Hence the integral operator fixes that unit.
(6) Theta_E, point transport and the exchange are the recorded scalar localizations.
The rational tensor comparison sends the integral unit tensored with 1 to oneRational.
The projection-normalized H⁰ comparison above identifies precisely this class in the
whole-system presentation of globalGeometricFrobeniusOnCohomology. Thus F(1_E)=1_E. -/
theorem frobenius_fixes_unit_section (c₀ : Compactification Y₀.hom) :
    (globalGeometricFrobeniusOnCohomology D c E Y₀ c₀
      (constantWeilRationalComplex c.l E.val D c.different Y₀) 0).1
        ((frobeniusUnitH0Comparison D c E Y₀ c₀).hom
          (oneRational D c.l c.different E.val (D.geometricFiber Y₀).left)) =
      (frobeniusUnitH0Comparison D c E Y₀ c₀).hom
        (oneRational D c.l c.different E.val (D.geometricFiber Y₀).left) := by
  sorry

end WeilConjectures
