/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite-extension specialization and scalars for the published complete category

Source: Weil blueprint, proper base change, order 1300
(blueprint: def-weil-pbc-bounded-constructible-complete).
The category is the published PbcIsBoundedConstructibleComplete, specialized to the
actual unlifted valuation ring in Type (u+1). Its completion, uniform reductions and
compatible origins are reused without redefining them. The published finite-extension
convenience abbreviation instead takes E in Type u and lifts its valuation ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u})

end AlgebraicGeometry.Scheme
