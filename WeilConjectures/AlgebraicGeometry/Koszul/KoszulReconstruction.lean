/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionComparison
/-! # Koszul reconstruction from strict quotient reductions

Source: blueprint order 1248; Stacks Tags 091N, 0941, 099M
(blueprint: prop-weil-pbc-koszul-reconstruction).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
