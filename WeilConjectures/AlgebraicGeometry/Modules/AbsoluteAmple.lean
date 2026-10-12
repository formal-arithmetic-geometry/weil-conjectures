/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Ample invertible modules on schemes (absolute ampleness)

This file defines the absolute notion of ampleness of Stacks, Properties, Definition 01PS
(EGA II 4.5.3): an invertible module `L` on a quasi-compact scheme `X` is ample if every point
lies in an affine nonvanishing locus `X_s` of a section `s` of some positive tensor power of `L`.

This is different from `AlgebraicGeometry.IsAmple`, which is defined relative to a base field via
the twisting sheaf of an embedding into projective space.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`: the locus `X_s` of a global section.
- `AlgebraicGeometry.Scheme.Modules.IsAmple`: absolute ampleness.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The nonvanishing locus `X_s` of a global section `s` of an `𝒪_X`-module `M`: the points `x`
where the germ of `s` is not in `𝔪_x M_x`, equivalently where `s` has nonzero value in the fibre
`M_x ⊗ κ(x)`. Source: Stacks Project, Properties, Section 01PR
(blueprint: `def-weil-pbc-ample-invertible-module`). -/
def nonvanishingLocus {X : Scheme.{u}} (M : X.Modules)
    (s : M.val.presheaf.obj (Opposite.op ⊤)) : Set X :=
  {y | (TopCat.Presheaf.germ M.val.presheaf ⊤ y trivial) s ∉
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
      (⊤ : Submodule (X.presheaf.stalk y) ↑(TopCat.Presheaf.stalk M.val.presheaf y))}

/-- An invertible `𝒪_X`-module `L` is *ample* (in the absolute sense) if `X` is quasi-compact and
for every `x : X` there are `n ≥ 1` and a global section `s` of `L^{⊗ n}` such that the
nonvanishing locus `X_s` is an affine open containing `x`.
Source: Stacks Project, Properties, Definition 01PS; EGA II 4.5.3
(blueprint: `def-weil-pbc-ample-invertible-module`). -/
def IsAmple (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible] : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 0 < n ∧
    ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤), ∃ U : X.Opens,
      x ∈ U ∧ IsAffineOpen U ∧ (U : Set X) = nonvanishingLocus (L.tensorPow n) s

end AlgebraicGeometry.Scheme.Modules
