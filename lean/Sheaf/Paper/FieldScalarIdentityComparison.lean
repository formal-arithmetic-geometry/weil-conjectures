/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Sheaf.Paper.FieldScalarNormalizedData

/-! # Identity field-scalar comparison

Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-identity-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.FieldScalar

/-- Every normalized scalar datum for the identity inclusion has its multiplication unitor.
Source: latest blueprint, sk-lem-sp-field-extension-towers.proof.md, paragraph (1).
(blueprint: lem-sp-field-scalar-identity-comparison).

Proof:
The residue-class normalization makes each quotient coefficient map the identity.
Its completed map is also the identity, since the reduction projections are jointly
monic and the coefficient comparisons are normalized on constants. Multiplication
r tensor x maps to r times x identifies integral scalar extension with the identity.
At each level the same multiplication, transported through extension.level, gives a
map from the extended system to the original one. The transition formula makes these
maps a morphism of whole systems. Insertion of one is the inverse; the tensor universal
property proves both equations and naturality. Pass these ordinary unitors to complexes.
The exact tower extension counit and the identity scalar counit are invertible on all
complexes. Localization therefore gives the two derived unitors with precisely the
representative equations. The reduction square on a flat K-flat complex is multiplication
of the same coefficients in either order. ReductionComparison.representative and the
universal derived properties extend this equality to all derived objects and roofs.
There is no field enlargement, choice of basis compatibility, or composition assertion. -/
theorem field_scalar_identity_comparison {l : ℕ} [Fact l.Prime] {E : Type u}
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{u}}
    {DA : SpCoefficientTowersAbelian.{u, u} l E T} {RA : SpReductionTower l E T DA}
    (D : ScalarData l E E (AlgHom.id (Padic l) E) T DA DA RA RA) :
    Nonempty (Identity D) := by sorry

end AlgebraicGeometry.ProEtale.FieldScalar
