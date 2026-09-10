/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometric reducedness is stable under composition

`Mathlib.AlgebraicGeometry.Geometrically.Irreducible` and
`Mathlib.AlgebraicGeometry.Geometrically.Connected` both record that their property is stable
under composition, but `Mathlib.AlgebraicGeometry.Geometrically.Reduced` does not. This file
supplies the missing statement, in the form in which
`AlgebraicGeometry.GeometricallyIntegral.comp` needs it.

## Main statements

- `AlgebraicGeometry.GeometricallyReduced.comp`: if `f` is flat and geometrically reduced and `g`
  is geometrically reduced and locally of finite type, then `f ≫ g` is geometrically reduced.

The flatness of `f` and the finite type of `g` are inherited from Mathlib's
`GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian`, which needs a flat morphism onto
a locally noetherian base; both hold in the intended application, where `g` is the structure
morphism of a variety over a field and `f` is a base change of one.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- Geometric reducedness is stable under composition, provided the first morphism is flat and
the second is locally of finite type. -/
lemma GeometricallyReduced.comp (f : X ⟶ Y) (g : Y ⟶ Z) [GeometricallyReduced f] [Flat f]
    [GeometricallyReduced g] [LocallyOfFiniteType g] :
    GeometricallyReduced (f ≫ g) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x ↦ ?_⟩
  have hred : IsReduced (pullback g x) :=
    pullback_of_geometrically ‹GeometricallyReduced g›.geometrically_isReduced K x
  have : IsLocallyNoetherian (pullback g x) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g x)
  exact ObjectProperty.prop_of_iso (C := Scheme.{u}) (IsReduced ·)
    (pullbackRightPullbackFstIso g x f) inferInstance

end AlgebraicGeometry
