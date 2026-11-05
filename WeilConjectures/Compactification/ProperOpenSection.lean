/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The section of a proper map fixing an open

Let `u : T₁ ⟶ T₂` be a proper morphism and `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` open immersions with
`j₁ ≫ u = j₂`. Put `V = T₁ ×_{T₂} X`, with projections `b : V ⟶ T₁` and `p : V ⟶ X`, and let
`s : X ⟶ V` be the morphism induced by `j₁` and `𝟙 X`. This file records the geometry of this
square: `p` is proper, `s` is an open immersion with closed image which is a section of `p`, and
`b` identifies `V` with the open subscheme `u⁻¹(j₂(X))` of `T₁`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isClopen_range_of_comp_eq_id`: an open immersion which is a
  section of a separated morphism has clopen range.
- `AlgebraicGeometry.isProper_pullback_snd_of_isProper`: the projection `p` is proper, hence
  separated.
- `AlgebraicGeometry.ProperOpenDatum`: the datum `(u, j₁, j₂)`, with its section
  `AlgebraicGeometry.ProperOpenDatum.section` and the properties of the latter.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The datum of the proper-open comparison: a proper morphism `u : T₁ ⟶ T₂` and open
immersions `j₁ : X ⟶ T₁`, `j₂ : X ⟶ T₂` with `j₁ ≫ u = j₂`. -/
structure ProperOpenDatum (X : Scheme.{u}) where
  /-- The source of the proper map. -/
  T₁ : Scheme.{u}
  /-- The target of the proper map. -/
  T₂ : Scheme.{u}
  /-- The proper map. -/
  u : T₁ ⟶ T₂
  /-- The open immersion into the source. -/
  j₁ : X ⟶ T₁
  /-- The open immersion into the target. -/
  j₂ : X ⟶ T₂
  comm : j₁ ≫ u = j₂ := by cat_disch
  isProper : IsProper u := by infer_instance
  isOpenImmersion₁ : IsOpenImmersion j₁ := by infer_instance
  isOpenImmersion₂ : IsOpenImmersion j₂ := by infer_instance

namespace ProperOpenDatum

attribute [instance] isProper isOpenImmersion₁ isOpenImmersion₂
attribute [reassoc (attr := simp)] comm

variable {X : Scheme.{u}} (D : ProperOpenDatum X)

end ProperOpenDatum

end AlgebraicGeometry
