/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Adjunction.Unique

import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralSupportFunctorNormalization
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Shift.Localization
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Normalized rational localization and cross-object orthogonality

Source: main-20261015, sec-smooth-purity/sk-prop-sf-localization,
prop-sf-open-closed-triangle-all-stages.proof.md, rational-stage paragraph
(blueprint: lem-sf-rational-localization-triangle-orthogonality).

The assertions retain the published pullback, compact-support and whole-system direct
image. The integral adjunction maps are fixed by their coherent-system normalization.
Rational adjunctions act on every tensor-Hom arrow. No Karoubi envelope is taken.
-/

@[expose] public noncomputable section
attribute [-instance] WeilConjectures.IntegralSupportNormalization.limitShift
  WeilConjectures.IntegralSupportNormalization.reductionShift
  WeilConjectures.IntegralSupportNormalization.directShift
  WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option autoImplicit false
attribute [local irreducible] WeilConjectures.sfIntegralConstructible
  WeilConjectures.sfRationalTriangulationDatum
  WeilConjectures.FrobeniusExchange.models
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe r u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section Geometry
variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (.of k))]
  [∀ x : U, Invertible (l : U.residueField x)]
  [∀ x : X, Invertible (l : X.residueField x)]

end Geometry

open CategoryTheory.ScalarLocalization

end WeilConjectures
