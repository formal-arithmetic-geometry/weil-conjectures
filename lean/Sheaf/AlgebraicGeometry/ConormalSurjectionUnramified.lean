module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # A conormal surjection detects unramifiedness

Source: Stacks Project, Morphisms, Tags 067L, 02GF and 01R4; the same argument occurs
in Resolution of Surfaces, Tag 0C5R
(blueprint: lem-sfb-conormal-surjection-unramified).

The conormal map is the unique map characterized in the recorded functoriality theorem.
The inverse of the canonical identity-pullback isomorphism identifies its source with
`j`'s conormal module. Surjectivity is sheaf surjectivity, expressed by `Epi`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- If the canonical conormal map for two closed immersions of the same scheme is
surjective, a locally finite type ambient map is unramified near every point of that scheme.
Source: Stacks Project, Morphisms, Tags 067L, 02GF and 01R4; Resolution of Surfaces, 0C5R
(blueprint: lem-sfb-conormal-surjection-unramified).

Proof:
1. Apply `lem-sfb-two-closed-immersions-conormal-exact` to obtain the right-exact sequence
   from the canonical conormal map to `i`'s conormal module and then to the pullback of
   the relative differential sheaf. Its first arrow is precisely the map used here,
   after the canonical identification of identity pullback with the original module.
2. The assumed sheaf surjectivity of the first arrow forces the second arrow to be zero.
   Its surjectivity then forces the pullback of the differential sheaf to be zero.
   This is a cokernel calculation and uses no flatness.
3. Fix `z` and set `x = i z`. By `lem-weil-pbc-module-stalk-pullback`, the zero stalk is
   the tensor of the differential stalk at `x` with the local ring at `z`. Tensoring
   further with the residue field at `z` gives a zero cotangent fibre. The closed
   immersion induces a surjective local-ring map, so its residue-field map is an
   isomorphism: for a local ring `A` and a proper ideal `K`, the residue field of
   `A/K` is canonically that of `A`. Thus the cotangent fibre at `x` is zero.
   These tensor products are the extension of scalars of `def-weil-module-base-change`.
4. Apply `lem-sfb-unramified-cotangent-fibre-criterion` to `f` and `x`, using the given
   local finite type hypothesis and the zero cotangent fibre. It gives the required
   open neighbourhood over the original target `Y`. For empty `Z` the conclusion is vacuous. -/
theorem isUnramified_near_of_conormal_surjective
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (i : Z ⟶ X) (j : Z ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (h : i ≫ f = j)
    (hsurj : Epi
      ((tensorPullbackSectionId Z).inv.app ((tensorPullback j).obj j.ker.toModules) ≫
        Classical.choose ((Classical.choose_spec
          (closedImmersion_conormal_functorial i j f (𝟙 Z)
            (h.trans (Category.id_comp j).symm)).2).2))) :
    ∀ z : Z, ∃ W : X.Opens, i z ∈ W ∧ IsUnramified (W.ι ≫ f) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
