/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs

/-! A finite locally constant set sheaf has finitely generated geometric stalks.

This is the intermediate finiteness assertion used to obtain finite stalks.
(blueprint: lem-galois-flc-set-is-finite-sheaf)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: lem-galois-flc-set-is-finite-sheaf) The finite locally constant
trivializations imply `IsFiniteSheaf`.

The proof follows the Stacks Project's reindexing argument for geometric stalks:
lift a geometric point to a member of the etale cover, identify the restricted
stalk with the stalk of the finite constant model, and use the constant
presheaf's terminal pointed neighbourhood. The proof reindexes pointed etale neighbourhoods
along a fibre product after lifting each
geometric point to a cover member. The resulting surjection from the restricted stalk, the
local constant-sheaf isomorphism, and the finite constant value show that every stalk is
finitely generated, which is exactly `IsFiniteSheaf` for types. -/
theorem isFiniteSheaf_of_finite_locally_constant_sets {Y : Scheme.{u}}
    (F : Sheaf Y.smallEtaleTopology (Type (u + 1)))
    (hF : ∃ 𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
      ∀ i, ∃ S : Type (u + 1), Finite S ∧
        Nonempty ((F.over (𝒰.etalePrecoverageToEtale i)) ≅
          (constantSheaf
            (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
            (Type (u + 1))).obj S)) : IsFiniteSheaf F := by
  sorry

end AlgebraicGeometry.Scheme
