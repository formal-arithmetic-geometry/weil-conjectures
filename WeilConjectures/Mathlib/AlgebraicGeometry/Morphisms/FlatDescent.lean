/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Flatness, affineness and finiteness satisfy fpqc descent

- `AlgebraicGeometry.Flat.descendsAlong_surjective_inf_flat_inf_quasicompact`: flatness of
  morphisms of schemes descends along faithfully flat quasi-compact morphisms.
- `AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact`: so does
  being affine (Stacks 02L5).
- `AlgebraicGeometry.IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact`: so does
  being finite (Stacks 02LA).
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
/-- Flatness satisfies fpqc descent. -/
@[stacks 02L2]
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

/-- **Being affine satisfies fpqc descent.** If the base change of `f : X ⟶ Y` along a
faithfully flat quasi-compact morphism is affine, then `f` is affine. -/
@[stacks 02L5]
theorem IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsAffineHom (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  sorry

/-- **Being finite satisfies fpqc descent.** A morphism is finite if and only if it is
universally closed, affine and locally of finite type, and each of these properties descends. -/
@[stacks 02LA]
theorem IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  rw [IsFinite.eq_inf, IsIntegralHom.eq_universallyClosed_inf_isAffineHom]
  infer_instance

end AlgebraicGeometry
