/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerConstructible
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueLayerVanishing

/-! # The residue layers of the target coefficient filtration

Source: Stacks, sites-modules, lemma-tensor-product-locally-constant;
proetale, lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layers).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

end WeilConjectures
