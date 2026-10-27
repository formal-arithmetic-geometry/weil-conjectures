/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FieldShriekSystemCoherence

/-! # Whole-system proper/open coefficient cocycles

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
proof steps 5--7 of lem-sp-field-shriek-system-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

/-- The normalized proper/open comparison satisfies composition and identity before
finite evaluation. No finite comparison or invertibility is asserted here.

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md (2),
lem-sp-field-shriek-system-comparison, steps 5--7
(blueprint: lem-sp-field-shriek-system-cocycle).

Proof: the residue-class formulas of Coefficients identify the composite and identity
quotient maps, hence the whole ring-system maps. On simultaneous flat-term K-flat
models both scalar/pullback paths send a nested tensor (x tensor s) tensor t to
V(x) tensor image(s)t. The representative equations in PullComparison and the
normalized derived scalar associator identify this calculation with the specified
whole-system scalarAssoc. Mate pasting gives the proper-factor cocycle and identity.
For the open factors, the open-unit normalization identifies both paths with the
same open adjunction mate; equivalently the open tensor generator formula sends
([x] tensor s) tensor t to [x tensor image(s)t]. Tensor unitors give the identity.
In the composite of two comparisons, naturality of the second proper mate moves
the first open map past it. Substitute the proper and open cocycles, and functoriality
combines the proper images of the open maps. The result is the displayed composition
in CoherenceLaw, with scalarAssoc on source and target. The same calculation with
the two unitors proves its identity clause. No equality is inferred from finite
evaluations. -/
theorem field_shriek_system_cocycle (P : PurityFiniteSetting.{u}) (D : Models P)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Nonempty (CoherenceLaw P D c) := by sorry

end AlgebraicGeometry.ProEtale.FieldShriekSystem
