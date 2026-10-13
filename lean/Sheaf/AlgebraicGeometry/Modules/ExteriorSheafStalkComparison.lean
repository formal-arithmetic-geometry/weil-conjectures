/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-!
# Exterior powers commute with module stalks

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph.
(blueprint: lem-sc-exterior-sheaf-stalk-comparison).
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- The exterior stalk comparison, characterized on wedges of germs.

Source: blueprint, Riemann--Roch, proof of (*), determinant paragraph; the finite
presentation argument in step 2 of `lem-sc-exterior-tensor-stalk-kernel-span`.
(blueprint: lem-sc-exterior-sheaf-stalk-comparison).

Proof: Present the exterior power by tuples, additivity in each coordinate,
scalar multiplication in each coordinate, and vanishing on repeated entries.
Every finite tuple of germs and every scalar has representatives on a common
neighborhood. Thus sending a sectionwise wedge to the wedge of its germs
induces a linear map from the stalk of the exterior presheaf to the exterior
power of the module stalk. Conversely, represent a tuple on a common
neighborhood and take the germ of its wedge. Two choices agree after restriction
to a common neighborhood, since equality of each of finitely many germs can
be realized there. The presentation relations hold for these germs, so this
extends linearly and is inverse to the first map. Sheafification leaves stalks
unchanged; its stalk map is linear by the scalar germ formula. Composing its
inverse with the first map gives the stated equivalence and formula. For n=0
both maps send the empty wedge to the empty wedge, and for a zero stalk ring
all the modules are zero. No local freeness or exactness is needed. -/
theorem exteriorSheaf_stalk_comparison {X : Scheme.{v}} (M : X.Modules)
    (n : ℕ) (x : X) :
    ∃ e : (exteriorSheaf M n).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
        ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x),
      ∀ (U : X.Opens) (hx : x ∈ U) (a : Fin n → M.val.obj (op U)),
        e ((exteriorSheaf M n).presheaf.germ U x hx (exteriorSheafSection M n U a)) =
          exteriorPower.ιMulti (X.presheaf.stalk x) n
            (fun i ↦ M.presheaf.germ U x hx (a i)) := by sorry

end AlgebraicGeometry.Scheme.Modules
