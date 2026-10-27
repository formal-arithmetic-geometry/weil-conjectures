/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U7
-/
module

public import Sheaf.SixFunctors.ProperOpenProjectionMate

/-! # Invertibility of the ordinary proper/open mate

Source: Stacks 0F7B, the support argument for a proper/open square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

/-- The canonical proper/open mate is invertible on arbitrary unbounded inputs.
Source: Stacks 0F7B
(blueprint: lem-sf-ordinary-proper-open-invertibility).

Proof: factor the source open through the Cartesian pullback of the target open.
The resulting lift is clopen: it is open by cancellation, and proper by cancellation
against the separated proper map. Proper/open support shows that the proper image
of an open extension lies in the essential image of target extension by zero.
For sheaves this follows from the Cartesian proper/open comparison; injective
acyclicity gives it for bounded-below complexes. Exact countable products and
lower Postnikov completeness extend support to arbitrary complexes. The canonical
mate's open adjunct is inverse lambda, where lambda is obtained by restricting
proper image, identifying the clopen extension with direct image, and composing
direct images. The inverse Hom bijection expresses this mate as extension of
inverse lambda followed by the supported open counit. Both factors are invertible.
-/
theorem ordinaryProperOpenMateIsIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsIso (properOpenMate A k r p i h) := by sorry

end AlgebraicGeometry.ProEtale
