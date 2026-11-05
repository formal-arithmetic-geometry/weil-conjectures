/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated

public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
/-! # Rationalization of the intrinsic integral constructible category

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460; current main snapshot, sec-proetale-coefficients/sk-def-sf-operations,
order 1819 (blueprint: def-weil-rationalization-karoubi).

Specialize the existing raw scalar localization to `sfIntegralConstructibleCategory`.
Its objects are unchanged and its Hom groups are tensor products with the localized
coefficient ring, canonically identified with E. No idempotents are adjoined.
The global finite-field datum only restricts the coefficient prime: it imposes no
structure morphism or finite-type condition on Y. The intrinsic category therefore
omits that unused datum; the scalar transition accepts its characteristic p and l ≠ p.
The legacy declarations are preserved by the public import.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory TensorProduct

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (p : ℕ) (hl : l ≠ p)
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

end WeilConjectures
