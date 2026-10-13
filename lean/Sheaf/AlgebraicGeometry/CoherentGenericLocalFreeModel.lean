/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A local free model along an integral closed subscheme

Source: Stacks Project, Tag 01YE, the argument before clearing denominators.
(blueprint: lem-pc-c3-coherent-generic-local-free-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A maximal-ideal-annihilated generic stalk has a local model by the closed
pushforward of a finite free module. This asserts no global map or ideal lattice.

Source: Stacks Project, Tag 01YE, first paragraphs through the local free map.
(blueprint: lem-pc-c3-coherent-generic-local-free-model)

Proof: put J equal to the defining ideal of i and take the subsheaf F' of sections
annihilated by J. It is quasi-coherent, hence coherent as a submodule of F on the
Noetherian scheme. The stalk of J at the image of the generic point is the maximal
ideal: the surjective closed-immersion stalk map has as quotient the function field
of integral Z. The annihilator stalk formula and hkill therefore identify F'_x
with F_x. The coherent inclusion F' -> F is an isomorphism near x. Closed-immersion
descent identifies F' with i_*G for a coherent module G on Z. Its generic stalk is
a finite vector space over the function field. Choose its finite dimension r and
a basis. Extend the corresponding isomorphism from the stalk of O_Z^{direct sum r}
to G to a map on an open V containing the generic point, then shrink V so that the
map is an isomorphism. Closed pushforward turns this into an isomorphism over
X minus i(Z minus V). Intersect this open with the neighbourhood on which F' -> F
is an isomorphism. Restriction and pushforward of the finite free module identify
the resulting source with the displayed restriction, giving the required iso.
For a zero generic stalk use r = 0: coherence makes F vanish near x. Z is
Noetherian since it is a closed subscheme of Noetherian X. No support assumption
on F is used, and no extension of this local isomorphism to X is asserted. -/
theorem coherent_generic_local_free_model
    {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0) :
    ∃ (r : ℕ) (U : X.Opens), i.base (genericPoint Z) ∈ U ∧
      Nonempty ((restrictFunctor U.ι).obj
        ((pushforward i).obj (∐ fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf)) ≅
        (restrictFunctor U.ι).obj F) := by sorry

end AlgebraicGeometry.Scheme.Modules
