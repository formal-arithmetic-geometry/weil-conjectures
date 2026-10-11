/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Ample invertible modules on schemes

Source: Stacks Project, Properties, Section 01PR and Definition 01PS
(blueprint: def-weil-pbc-ample-invertible-module).
-/

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The absolute ampleness condition of Stacks Properties Definition 01PS.
The open `U` is exactly the locus where the germ is outside the maximal ideal times
the stalk module, equivalently where the section has nonzero residue-field value.
Source: Stacks Project, Properties, Definition 01PS
(blueprint: def-weil-pbc-ample-invertible-module).
-/
def IsAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible] : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 0 < n ∧
    ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ ∀ y : X, y ∈ U ↔
        (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf ⊤ y trivial) s ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y)
              ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf y))

end AlgebraicGeometry.Scheme.Modules
