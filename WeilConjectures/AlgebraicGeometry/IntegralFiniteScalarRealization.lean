/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectReductionHomML
public import Mathlib.Algebra.Category.ModuleCat.Ulift
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import all WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution

/-! # Exact realization of small scalar complexes at the finite integral levels

Source: current blueprint, sk-prop-integral-local-structure, finite-level comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Realize small scalar modules by continuous coefficients on a scheme.
The finite coefficient quotient carries its actual quotient topology.
Source: blueprint sk-prop-integral-local-structure, finite-level comparison
(blueprint: def-pe-integral-finite-scalar-realization). -/
def integralFiniteScalarFunctor (W : Scheme.{u}) (n : ℕ) :
    ModuleCat.{u} (Padic.coefficientExtensionRing l E (n + 1)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
        (AdicCompletion.finiteRing l E W n) :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  ModuleCat.uliftFunctor.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    FiniteConstantModel.modelFunctor (Padic.coefficientExtensionRing l E (n + 1)) W

instance (W : Scheme.{u}) (n : ℕ) :
    (integralFiniteScalarFunctor l E W n).Additive :=
  (finiteScalar_assertions l E W n).1

instance (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteLimits (integralFiniteScalarFunctor l E W n) :=
  (finiteScalar_assertions l E W n).2.1

instance (W : Scheme.{u}) (n : ℕ) :
    PreservesFiniteColimits (integralFiniteScalarFunctor l E W n) :=
  (finiteScalar_assertions l E W n).2.2

/-- Exact scalar realization on the derived categories, using the actual finite
quotient coefficient ring.
Source: blueprint sk-prop-integral-local-structure, finite-level comparison
(blueprint: def-pe-integral-finite-scalar-realization). -/
def integralFiniteScalarRealization (W : Scheme.{u}) (n : ℕ) :=
  (integralFiniteScalarFunctor l E W n).mapDerivedCategory

end AlgebraicGeometry.ProEtale
