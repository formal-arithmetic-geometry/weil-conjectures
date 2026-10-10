/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Hopf algebra structure on `SymmetricAlgebra R M`

Over a commutative ring, the bialgebra `SymmetricAlgebra R M`, in which every generator `ι x` is
primitive, is a Hopf algebra with antipode `ι x ↦ -ι x`. For `M = R` this is the coordinate ring
`R[y]` of the additive group `𝔾ₐ`.

## Main definitions

- `SymmetricAlgebra.antipodeAlgHom`: the antipode `ι x ↦ -ι x`.
- `SymmetricAlgebra.instHopfAlgebra`: the Hopf algebra structure.
-/

@[expose] public section

noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-- The antipode of `SymmetricAlgebra R M`: the algebra endomorphism `ι x ↦ -ι x`. -/
def antipodeAlgHom : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M :=
  lift (-ι R M)

@[simp]
theorem antipodeAlgHom_ι (x : M) : antipodeAlgHom R M (ι R M x) = -ι R M x := by
  simp [antipodeAlgHom]

/-- `SymmetricAlgebra R M` is a Hopf algebra, with antipode `ι x ↦ -ι x`. -/
instance instHopfAlgebra : HopfAlgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom (antipodeAlgHom R M) (by ext x; simp) (by ext x; simp)

@[simp]
theorem antipode_ι (x : M) : HopfAlgebra.antipode R (ι R M x) = -ι R M x :=
  antipodeAlgHom_ι R M x

end SymmetricAlgebra
