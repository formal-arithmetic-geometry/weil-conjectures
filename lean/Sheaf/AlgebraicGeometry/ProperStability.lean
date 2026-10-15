/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Stability of proper morphisms

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
lemma "Properness survives base change and composition" (blueprint: lem-kun-proper-stability).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper morphisms are stable under base change and composition; in particular the second
projection from the product of a proper `k`-scheme with any `k`-scheme is proper.
Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
lemma "Properness survives base change and composition" (blueprint: lem-kun-proper-stability).

Proof: use `lem-weil-pbc-proper-base-change` for arbitrary base change and
`lem-weil-pbc-proper-composition` for composition. Apply the former with the proper structure
map `f : X ⟶ Spec k` and the arbitrary structure map `g : Y ⟶ Spec k`. Their fibre product
is `X ×_k Y` and its base-changed structure map is exactly `pullback.snd f g`, the second
projection, proving the last clause. -/
theorem proper_stability :
    MorphismProperty.IsStableUnderBaseChange (@IsProper.{u}) ∧
    MorphismProperty.IsStableUnderComposition (@IsProper.{u}) ∧
    (∀ (k : Type u) [Field k] (X Y : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)),
      IsProper f → IsProper (pullback.snd f g)) := by
  sorry

end AlgebraicGeometry
