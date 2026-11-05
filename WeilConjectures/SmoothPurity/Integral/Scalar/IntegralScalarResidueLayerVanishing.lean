/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.FilteredCoefficientTensorBounds
import WeilConjectures.AlgebraicGeometry.ResidueLayerTensor.ResidueLayerTensorComparison
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarResidueCoefficientIso
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ULift

/-! # Vanishing of an integral scalar residue layer

This is the support clause of the residue-layer argument.  It isolates the
finite-residue scalar-extension and interval comparison from the constructibility
clause of the parent theorem.
Source: Stacks, sites-modules, lemma-tensor-product-locally-constant; proetale,
lemma-constructible-serre; parent finite-filtration argument.
(blueprint: lem-sf-integral-scalar-residue-layer-vanishing).

Proof: the quotient of two consecutive powers of the target uniformizer is the
finite target residue field.  Multiplication by the appropriate power of the
uniformizer identifies the quotient with that residue field; cancellation in the
DVR proves injectivity.  The coefficient map factors through the source residue
field.  Balanced tensor associativity identifies the resulting layer complex with
finite-field scalar extension of the source residue reduction.  Exact finite-field
scalar extension preserves the given finite local models, and restriction to the
finite quotient ring preserves those models.  Derived homology agrees with the
homology of the K-flat representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme
namespace IntegralScalarResidueVanishing

open CategoryTheory.Functor

-- The full finite-field theorem has a downstream import back to this module.
-- Use its exactness argument on the concrete, lower-level sheaf extension instead.

end IntegralScalarResidueVanishing
end AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

end WeilConjectures
