/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PairingFiniteTensorNormalization

/-! # Normalized finite tensor coordinates for the pairing

Source: main-20261015, sec-poincare-duality/sk-def-pairing-data/_section.md,
first displayed composite; Stacks Tags 00YV, 0GMW and 06YN.
(blueprint: def-pod-pairing-finite-tensor-transport).
The comparison is determined on every K-flat representative by its value on
local pure tensors, including the signed total differential.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- The normalized comparison is unique, including its values on every K-flat
pair, rather than an arbitrary isomorphism of the two derived bifunctors.
Source: Stacks 00YV, 0GMW, 06YN and 06YU
(blueprint: def-pod-pairing-finite-tensor-transport).
Proof: the scalar-unit sections locally generate realization. Sheafification
therefore gives exactly one tensor map sending each such pure tensor to the
same tensor of realized sections. Its inverse is given by the inverse
sheafification tensor comparison. Sum over all bidegrees; naturality preserves
the differential and its Koszul sign. The exact equivalence preserves K-flat
resolutions. The two universal derived tensor comparisons descend this chain
isomorphism. Every pair has such a resolution, so the displayed square fixes
every component and gives uniqueness. -/
theorem pairingFiniteRealizationTensor_existsUnique :
    ∃! e : PairingRealizationTensorComparison l E X m,
      PairingRealizationTensorNormalized l E X m e := by
  sorry

/-- The tensor comparison with the preceding representative normalization.
Source: first cup display (blueprint: def-pod-pairing-finite-tensor-transport). -/
def pairingFiniteRealizationTensor :=
  (pairingFiniteRealizationTensor_existsUnique l E X m).exists.choose

end WeilConjectures
