/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.NoetherianSpace

/-! # Open–closed factorization of immersions into Noetherian schemes

An immersion into a scheme with Noetherian underlying space factors as an open immersion
followed by a closed immersion. This is the geometric input for extension along topologically
locally closed immersions.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-- An immersion `f : T ⟶ X` into a scheme with Noetherian underlying space factors as an open
immersion followed by a closed immersion. -/
theorem exists_open_closed_factorization {T X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X] (f : T ⟶ X) [IsImmersion f] :
    ∃ (Z : Scheme.{u}) (j : T ⟶ Z) (i : Z ⟶ X),
      IsOpenImmersion j ∧ IsClosedImmersion i ∧ j ≫ i = f := by
  let : TopologicalSpace.NoetherianSpace T := f.isEmbedding.isInducing.noetherianSpace
  let : QuasiCompact f := inferInstance
  exact IsImmersion.isImmersion_iff_exists_of_quasiCompact.mp inferInstance
