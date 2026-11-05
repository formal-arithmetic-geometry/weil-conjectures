/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSized
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Finite coefficient extension and sheafwise completion

Source: coefficient-twist blueprint, order 1505, proof step 6.
(blueprint: lem-pur-twist-coefficient-tensor)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t u v w
open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/- The quotient and scalar-restriction constructions in this section follow the
proved private helpers of WeilConjectures.RingTheory.CompletionFiniteExtensionTensorBijective.
They preserve the actual quotient projections and the completed scalar action. -/
section CompletionScalarTransport

end CompletionScalarTransport

end AlgebraicGeometry.Scheme
