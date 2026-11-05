/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated

public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
/-! # Rationalized constructible integral categories and coefficient extension

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1460 (blueprint: def-weil-rationalization-karoubi).

This is raw Hom scalar localization, with the same integral objects. The canonical
localization isomorphism identifies its Hom modules with Hom tensor E. No retracts
are adjoined. The coefficient functor is fixed uniquely on objects and pure tensors.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d u

open CategoryTheory TensorProduct

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

end WeilConjectures

namespace WeilConjectures

open CategoryTheory TensorProduct

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

end WeilConjectures
