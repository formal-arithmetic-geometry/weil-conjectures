/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayers
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarRegularTensorComparison
import Mathlib.Data.Int.Interval

/-! # Uniform constructibility of finite scalar tensor levels

Source: Bhatt--Scholze, Proposition 3.5.1; integral scalar constructibility proof.
(blueprint: lem-sf-integral-scalar-finite-level-bounds).
-/

@[expose] public section
set_option autoImplicit false

universe d u
open CategoryTheory AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

end WeilConjectures
