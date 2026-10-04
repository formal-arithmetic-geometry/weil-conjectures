/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension under quasi-finite morphisms

## Main statements

- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_eq_of_surjective`: a universally closed,
  locally quasi-finite, surjective morphism of schemes (for instance a finite surjective one)
  preserves the dimension.
-/

@[expose] public section

universe u

open Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A locally quasi-finite morphism identifies no two distinct points `x ⤳ x'`: its fibres are
discrete. -/
lemma Scheme.Hom.eq_of_specializes_of_apply_eq (f : X ⟶ Y) [LocallyQuasiFinite f] {x x' : X}
    (h : x ⤳ x') (hx : f x = f x') : x = x' := by
  have : DiscreteTopology (f ⁻¹' {f x'}) := (f.isDiscrete_preimage_singleton (f x')).to_subtype
  have h' : (⟨x, hx⟩ : f ⁻¹' {f x'}) ⤳ ⟨x', rfl⟩ := IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val h'.eq

/-- **A universally closed, locally quasi-finite, surjective morphism preserves the dimension.**
Such a morphism `f : X ⟶ Y`, for instance a finite surjective one, satisfies `dim X = dim Y`:
chains of specializations in `Y` lift to `X` since `f` is closed (going up), and their images in
`Y` stay strict since the fibres of `f` are discrete (incomparability). -/
theorem Scheme.Hom.topologicalKrullDim_eq_of_surjective (f : X ⟶ Y) [UniversallyClosed f]
    [LocallyQuasiFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y :=
  le_antisymm
    (topologicalKrullDim_le_of_continuous f.continuous fun _ _ ↦ f.eq_of_specializes_of_apply_eq)
    (topologicalKrullDim_le_of_specializingMap f.isClosedMap.specializingMap f.surjective)

end AlgebraicGeometry
