/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Geometry of a nonempty smooth geometrically connected family

Source: Stacks Project, Tags 034F, 056T and 01UA.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A nonempty smooth geometrically connected family over a normal integral base
and its generic fibre are normal integral with the same function field.

Source: Stacks Project, Tags 034F, 056T and 01UA.
(blueprint: lem-sbc-smooth-connected-generic-geometry)

Proof: Smoothness preserves normality (034F). The smooth fibres over fields
are geometrically normal and reduced (056T), and their geometric connectedness
therefore makes every nonempty fibre geometrically integral: on any affine
chart a normal ring has domain local rings, and the locally noetherian normal
scheme is the disjoint union of its irreducible components. Smoothness is open
(01UA). Since C is nonempty, its image is a nonempty open in the integral S,
so the generic fibre is nonempty. Flatness implies that this fibre is dense:
every nonempty open of C has open image meeting the generic point. The integral
generic fibre is normal by smoothness over a field. It makes C irreducible;
normality implies reducedness, so C
is integral. The generic point of C lies over that of S. Pullback by the generic
stalk map localizes the base at its generic point and leaves the stalk at C's
generic point unchanged. Thus C and Cη have isomorphic generic stalks. Their
spectra give the displayed isomorphism e, with the compatibility equation
by the stalk-map naturality and the cartesian square. -/
theorem smooth_connected_generic_geometry {S C : Scheme.{u}} [IsIntegral S]
    [Nonempty C] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [Smooth c] [GeometricallyConnected c]
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c) :
    ∃ hC : IsIntegral C, letI := hC;
      ∃ hη : IsIntegral Cη, letI := hη;
        (∀ x : C, IsIntegrallyClosed (C.presheaf.stalk x)) ∧
        (∀ x : Cη, IsIntegrallyClosed (Cη.presheaf.stalk x)) ∧
        ∃ e : Spec C.functionField ≅ Spec Cη.functionField,
          (e.hom ≫ Cη.fromSpecStalk (genericPoint Cη)) ≫ j =
            C.fromSpecStalk (genericPoint C) := by sorry

end AlgebraicGeometry.Scheme
