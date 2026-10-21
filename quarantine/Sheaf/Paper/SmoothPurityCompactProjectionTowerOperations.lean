/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F8
-/
module

public import Sheaf.Paper.SmoothPurityCompactProjectionData
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Operations on a normalized varying coefficient system

Source: Stacks 03D7, 07A4, 03DI, 0GL1 and the finite/tower construction in
blueprint `lem-sp-compact-projection-base-change`, proof step 1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules.OpenTensorNormalization
namespace AlgebraicGeometry.ProEtale.CompactProjectionBaseChange

/-- Simultaneous module and derived operations on a normalized varying coefficient system.
This concerns the operations after the actual coefficient system and its equivalence with
coefficient towers have been constructed. It does not assert existence of that system.
Source: blueprint coefficient-tower construction; Stacks 03D7, 03DI, 07A4 and 0GL1
(blueprint: lem-sp-compact-projection-tower-operations).

Proof: use inverse image on the vertical diagram site, leaving the coefficient index fixed.
The specified sectionwise coefficient maps identify inverse image of the ring sheaf with
the target ring sheaf. Module inverse image is therefore exact. The module adjunction,
K-injective resolutions and signed total tensor on flat-term K-flat resolutions supply
Operation and TensorModel. Tensor pullback is fixed by the pure-tensor unit formula and
its total-complex representative equation. The direct-image square is induced by the
iterated fibre-product comparison; evaluate it on sections to obtain rightSections.
For an open immersion use extension by zero on this same vertical site. Its adjunction
unit is invertible and the extension is exact. Open tensor normalization identifies the
inverse open projection mate and the inverse open base-change mate with the invertible
normalized comparisons. These constructions are simultaneous in the schemes and maps,
with one derived tensor model at each scheme. They preserve all coefficient transitions;
no scalar extension along quotient-ring reductions is used as an exact functor. -/
theorem normalized_tower_operations_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (c : Coefficients.{u} .systems) (_hc : TowerCoefficients l E c) :
    ∃ o : Presentation c, Nonempty (OpenComparisons o) := by sorry

end AlgebraicGeometry.ProEtale.CompactProjectionBaseChange
