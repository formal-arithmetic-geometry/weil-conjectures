module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Integrality from a schematically dense integral open

Source: Stacks Project, Morphisms, Tags 01RE and 01RV; Properties, Tag 01OK.
(blueprint: lem-sfb-schematic-integral-open-criterion)

The inverse image of an open under the open immersion represents its intersection with the
integral open subscheme. The map on sections followed by a germ is written as that composite.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A schematically dense integral open makes its ambient scheme integral, and the sections
of each nonempty affine open inject into the generic stalk of the integral open.
Source: Stacks Project, Morphisms, Tags 01RE and 01RV; Properties, Tag 01OK.
(blueprint: lem-sfb-schematic-integral-open-criterion)

Proof:
1. The integral scheme `V` is nonempty, hence so is `Z`. Choose a nonempty affine open of
   `V`. The affine fraction-field description (lem-sc-integral-function-field-affine-fraction,
   `functionField_isFractionRing_of_isAffineOpen`) shows that the stalk at its generic point
   `η` is a field, as in Tag 01RV.
2. For a nonempty affine open `W` of `Z`, schematic density gives an injective restriction
   `j.app W` (def-nagata-scheme-theoretically-dense-open, Tag 01RE). If its inverse image were
   empty, its section ring would be the zero ring, forcing the section ring of `W` to be
   the zero ring. This contradicts the existence of a point of the affine scheme `W`
   (def-weil-affine-spectrum).
3. The generic point `η` belongs to the nonempty inverse image of `W`: its closed complement
   cannot contain a point whose closure is all of `V` (def-sc-generic-point). The germ map
   on this open is injective by lem-sc-integral-scheme-stalks-in-function-field, clause 1
   (`germ_injective_of_isIntegral`). Composing with the injective restriction proves the
   asserted injectivity.
4. The section ring of each nonempty affine `W` embeds in this field, so it is a domain:
   injectivity detects `1 ≠ 0`, and a product mapping to zero has a factor mapping to zero.
   Together with nonemptiness of `Z`, this is integrality (def-pc-integral-scheme, Tag 01OK).
-/
theorem schematicIntegralOpenCriterion {Z V : Scheme.{u}} (j : V ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] [IsIntegral V]
    [IsSchemeTheoreticallyDominant j] (η : V) (hη : IsGenericPoint η Set.univ) :
    IsIntegral Z ∧ IsField (V.presheaf.stalk η) ∧
      ∀ (W : Z.Opens), IsAffineOpen W → Nonempty W →
        Nonempty (j ⁻¹ᵁ W) ∧
          ∃ hηW : η ∈ j ⁻¹ᵁ W,
            Function.Injective (j.app W ≫ V.presheaf.germ (j ⁻¹ᵁ W) η hηW) := by
  sorry

end AlgebraicGeometry
