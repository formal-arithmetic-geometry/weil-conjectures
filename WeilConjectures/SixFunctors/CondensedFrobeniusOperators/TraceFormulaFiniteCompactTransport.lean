/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedFiniteCohomologyTransport
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Finite condensed compact transport

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`
(blueprint: def-trf-finite-condensed-compact-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace WeilConjectures.CondensedFrobeniusOperators
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
/-- The closure in the finite-field datum is algebraically closed.
Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-cor-sp-all-coefficients/def-trf-frobenius-operators.md`,
clause (1).
(blueprint: def-trf-finite-condensed-compact-transport). -/
noncomputable instance finiteDatumIsAlgClosed (F : WeilConjectures.FiniteFieldDatum.{u}) :
    IsAlgClosed F.k := IsAlgClosure.isAlgClosed F.k₀

end WeilConjectures.CondensedFrobeniusOperators
