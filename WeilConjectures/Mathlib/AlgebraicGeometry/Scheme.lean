/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Preimages of opens under a morphism of schemes

Mathlib records that taking preimages of opens commutes with arbitrary suprema
(`AlgebraicGeometry.Scheme.Hom.preimage_iSup`). Infima of opens are only intersections when
indexed by a finite type, and in that case preimages commute with them as well:

- `AlgebraicGeometry.Scheme.Hom.preimage_iInf`.

We also record that a global section whose non-vanishing locus is everything is a unit:

- `AlgebraicGeometry.Scheme.isUnit_of_basicOpen_eq_top`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Taking preimages of opens commutes with finite infima. -/
lemma preimage_iInf {ι : Type*} [Finite ι] (U : ι → Y.Opens) :
    f ⁻¹ᵁ ⨅ i, U i = ⨅ i, f ⁻¹ᵁ U i :=
  Opens.ext <| by
    simp only [coe_preimage, Opens.coe_iInf, Set.preimage_iInter]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- A global section that vanishes nowhere is a unit. -/
lemma isUnit_of_basicOpen_eq_top {X : Scheme.{u}} (f : Γ(X, ⊤)) (h : X.basicOpen f = ⊤) :
    IsUnit f := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ ⊤ f fun x _ ↦ ?_
  exact (X.mem_basicOpen_top f x).mp (h.ge trivial)

end AlgebraicGeometry.Scheme
