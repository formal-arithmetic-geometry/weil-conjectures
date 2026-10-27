module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.RingHom.Flat

/-!
# Flat morphisms and maximal dominance under base change

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Definition 1.1.2,
Example 1.1.3 and Proposition 1.1.5, printed p. 23
(blueprint: lem-per-flat-maximal-dominance-base-change).

Maximal dominance is expressed directly using `IsGenericPoint` and
`irreducibleComponents`: each component-generic source point maps to a
component-generic target point.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Flat morphisms are maximally dominant, and maximal dominance survives flat base change.
Source: ILO, Travaux de Gabber, Exposé II, Example 1.1.3 and Proposition 1.1.5, p. 23
(blueprint: lem-per-flat-maximal-dominance-base-change).

Proof plan:
1. A scheme point is generic in an irreducible component exactly when it has no proper
   generalization. For the forward implication use maximality of the component and uniqueness
   of its generic point; for the reverse implication choose a component through the point
   and use scheme sobriety to obtain its generic point. These are
   `lem-sc-irreducible-components-cover` and `lem-sc-scheme-sober`.
2. For a flat morphism, lift a generalization of the image of a component-generic point
   using `lem-weil-pbc-flat-generalizations-lift`. Its lift must equal the original point,
   so its image has no proper generalization. Apply this to `h` for the first clause.
3. Put `Z = X ×[Y] Y'`, with projections `p` and `q`. The projection `p` is flat by
   `lem-weil-pbc-flat-morphism-base-change`. Thus for a component-generic `z`, the point
   `x = p z` is component-generic, and maximal dominance of `f` makes `y = f x` generic
   in a component of `Y`. Write `y' = q z`.
4. Identify the fibre `Z_x` with the base change of `Y'_y` along the residue-field map
   `κ(y) → κ(x)`, using the pullback universal properties. The induced map between these
   fibres is flat by `lem-pc-field-extension-flat` and flat base change. The fibre
   homeomorphisms of `def-pc-scheme-fibre` identify `z` and `y'` with points `w` and `t`
   of these fibres. Any generalization of `w` maps to a generalization of `z`, hence is
   `w`, since the fibre inclusion is injective. Consequently `w` is component-generic,
   and step 2 makes its image `t` component-generic.
5. Every generalization `v` of `y'` maps under `h` to a generalization of `y`, hence to
   `y` itself. Both points lie in the fibre over `y`. Specialization in a subspace is
   the ambient specialization restricted to that subspace, so the fibre homeomorphism
   sends `v` to a generalization of `t`. Step 4 forces equality, giving `v = y'`.
   Step 1 now makes `y'` component-generic, proving the base-change clause.
-/
theorem flat_maximalDominance_and_baseChange {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (h : Y' ⟶ Y) [Flat h] :
    (∀ C ∈ irreducibleComponents Y', ∀ η : Y', IsGenericPoint η C →
      ∃ D ∈ irreducibleComponents Y, IsGenericPoint (h η) D) ∧
    ((∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C →
      ∃ D ∈ irreducibleComponents Y, IsGenericPoint (f η) D) →
      ∀ C ∈ irreducibleComponents ↥(pullback f h), ∀ η : ↥(pullback f h),
        IsGenericPoint η C →
          ∃ D ∈ irreducibleComponents Y', IsGenericPoint (pullback.snd f h η) D) := by
  sorry

end AlgebraicGeometry
