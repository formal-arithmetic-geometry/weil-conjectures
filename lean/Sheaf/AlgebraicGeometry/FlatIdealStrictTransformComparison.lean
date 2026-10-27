/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleStrictTransform
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The strict transform of an ideal under a flat morphism

Source: Stacks Project, Divisors, Tags 080D and 080F; Modules, Tag 01AJ.
(blueprint: lem-per-flat-ideal-strict-transform-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The module strict transform of an ideal along a base blowup is its extended ideal
when the original scheme is flat over the base.

Source: Stacks Project, Divisors, Tag 080D (1), the supported-section quotient, and
Tag 080F, its regular exceptional-equation argument; Modules, Tag 01AJ.
(blueprint: lem-per-flat-ideal-strict-transform-comparison).

Proof: Put Y = X ×_S Bl_I(S), with projections p and g, and let E be the extended
centre on Bl_I(S). Principalization makes E Cartier. The morphism g is flat by base
change, so the structure module of Y is flat over Bl_I(S). The Cartier-support lemma
therefore makes restriction of this structure module to Y minus g⁻¹E injective on every
open. Let H = p* K and let alpha : H → O_Y be the pulled-back ideal inclusion.
The tensor-pullback ideal comparison identifies its image with (K.comap p).toModules.
Away from g⁻¹E, the blowup and p are isomorphisms, so alpha is injective there.
Thus ker alpha is contained in the kernel of restriction defining the strict transform.
Conversely a section in that restriction kernel has image under alpha vanishing off
g⁻¹E; injectivity of restriction for O_Y makes this image zero. The two kernels are
equal as subobjects of H. The first isomorphism theorem in the abelian module category
identifies the cokernel of the restriction-kernel inclusion with image alpha, and hence
with the extended ideal. All comparisons commute with ideal inclusions. The empty
blowup and the zero or unit ideal are covered by the same kernel calculation. -/
theorem nonempty_moduleStrictTransform_ideal_iso_comap
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (I : S.IdealSheafData) [I.toModules.IsFiniteType]
    (K : X.IdealSheafData) [K.toModules.IsQuasicoherent] :
    Nonempty (moduleStrictTransform f I K.toModules ≅
      (K.comap (pullback.fst f I.blowupMap)).toModules) := by sorry

end AlgebraicGeometry.Scheme.Modules
