/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Zero

/-!
# A sheaf with vanishing stalks is zero

Source: literature/blueprint/master/blueprint/sec-abelian-varieties/
sk-prop-av-pqf-finite/pqf-lem-sheaf-zero-stalks.md
(blueprint: pqf-lem-sheaf-zero-stalks)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A sheaf of modules on a scheme with zero stalk at every point is the zero sheaf.

Source: literature/blueprint/master/blueprint/sec-abelian-varieties/
sk-prop-av-pqf-finite/pqf-lem-sheaf-zero-stalks.md,
node pqf-lem-sheaf-zero-stalks (blueprint: pqf-lem-sheaf-zero-stalks).
Proof: for every open and section, the section has zero germ at each point by the stalk
hypothesis. The germ equality criterion gives a neighbourhood on which it vanishes. These
neighbourhoods cover the open, so separatedness of the underlying sheaf gives that the
section is zero; hence the module sheaf is a zero object. Uses def-weil-pbc-module-stalk and
def-weil-sheaf-of-modules-category. -/
theorem isZero_of_isZero_stalks (X : Scheme.{u}) (F : X.Modules)
    (hF : ∀ (x : X), IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) :
    IsZero F := by
  let G := SheafOfModules.toSheaf X.ringCatSheaf
  have hG : IsZero (G.obj F) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (G.obj F)).mpr
    intro x
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    change Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.toTopCat) F.val.presheaf x)
    exact ModuleCat.isZero_iff_subsingleton.mp (hF x)
  apply (IsZero.iff_id_eq_zero F).mpr
  apply G.map_injective
  rw [G.map_id, G.map_zero]
  exact (IsZero.iff_id_eq_zero (G.obj F)).mp hG

end AlgebraicGeometry.Scheme.Modules
