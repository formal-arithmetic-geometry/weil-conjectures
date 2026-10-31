/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Schematic density of an open subscheme

Source: Temkin, *Stable modification of relative curves*, §1.2
(blueprint: def-trf-schematically-dense-open).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An open subscheme is schematically dense when restriction of sections to it is
injective on every open of the ambient scheme. This is equivalent to injectivity of
`𝒪_Z → j_*𝒪_U` for an open immersion.
Source: Temkin, *Stable modification of relative curves*, §1.2
(blueprint: def-trf-schematically-dense-open). -/
def SchematicallyDenseOpen {Z : Scheme.{u}} (U : Z.Opens) : Prop :=
  ∀ W : Z.Opens,
    Function.Injective
      (Z.presheaf.map ((homOfLE (inf_le_left : W ⊓ U ≤ W))).op)

end AlgebraicGeometry
