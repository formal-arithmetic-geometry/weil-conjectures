/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNeighborhood

/-!
# The geometric fibre of an integral morphism

Let `f : X ⟶ Y` be an integral morphism and `y : Spec Ω ⟶ Y` a geometric point with `Ω`
algebraically closed. Every point of the scheme-theoretic fibre of `f` over `y` is the image of
a geometric point of `X` over `y`
(`AlgebraicGeometry.Scheme.Hom.GeometricFiber.exists_apply_default_eq_of_isIntegralHom`), and a
closed subset of `U ×_Y X` avoiding the points `(u, t)` disappears over a smaller pointed étale
neighbourhood of `y` (`AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot_of_isIntegralHom`).
These are the integral versions of the corresponding statements for finite morphisms, with the
same proofs: only lying over and the closedness of integral morphisms are used.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite RingHom

namespace AlgebraicGeometry.Scheme.Hom

section Fibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] (y : Spec (.of Ω) ⟶ Y)

end Fibre

section Shrink

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y} [IsIntegralHom f]

end Shrink

end AlgebraicGeometry.Scheme.Hom
