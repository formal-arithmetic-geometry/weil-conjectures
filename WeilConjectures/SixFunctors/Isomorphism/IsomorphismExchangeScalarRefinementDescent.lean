/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SixFunctors.Supporting.ExchangeFunctoriality
import all WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeGeometryFibreBound
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionPasting

public import WeilConjectures.SixFunctors.PurReindexing.SemilinearExchangeReindexingData
public import WeilConjectures.SixFunctors.Supporting.SemilinearExchangeDescentData
public import WeilConjectures.FourierTransform.FdCoefficientComparison

/-! # Scalar transport and compactification descent of isomorphism exchange

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility;
extracted scalar and refinement argument, Steps 1--9
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent).

Each conclusion below uses the specified completed exchange, its raw localization,
and the unit-normalized common-stage model. No rational reduction is introduced.
The hypotheses are the finite and actual strict integral normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
open WeilConjectures WeilConjectures.PurityFiniteSetting

namespace WeilConjectures

/-- Scalar localization carries the actual integral two-factor identity to the ordered
rational reindexing identity, with its quotient-completion unit and the original
constructible endpoints. The tuple may be any finite generating tuple.
Proof (Steps 1 and 5--6): identify both strict factors before Rlim by the supplied
normalization. Their derived limits are completedCompactSupportExchange. Substitute
the ordered identity into the prescribed localization of that map. Functoriality
preserves its two factors and all invertible endpoint comparisons; the inverse unit
fixes the isomorphism e uniquely. Fraction naturality is integral naturality multiplied
by the inverse uniformizer power. For coefficient change, commute through proper units
and counits and the open comparison; the adjacent scalar comparisons cancel. Their
cocycles make common-stage representatives independent of field enlargement. For
refinement apply the strict proper/open equation, its corner normalizations and Rlim,
then localize. Cancellation of the canonical comparison inverses gives independence,
the common-refinement cocycle and compatibility with the compact-support compositor.
Finite evaluation gives the finite formula, with the retained etale-origin witness.
No reduction is applied to a rational arrow.
Source: constituent-compatibility assembly, extracted scalar/refinement argument
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeScalarRefinementDescent
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearRational P ∧
      PurSemilinearScalar P ∧
      PurSemilinearCommonStage P ∧
      PurSemilinearRationalCoherence P ∧
      PurSemilinearRefinement P ∧
      PurSemilinearFiniteCompactComparison P := by
  sorry

end WeilConjectures
