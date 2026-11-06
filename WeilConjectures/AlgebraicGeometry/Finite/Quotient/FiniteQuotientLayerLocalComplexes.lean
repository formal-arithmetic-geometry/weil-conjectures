/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerLocalComplexCore

/-! # Local algebraic complexes for a coefficient-filtration outer term
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-local-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
