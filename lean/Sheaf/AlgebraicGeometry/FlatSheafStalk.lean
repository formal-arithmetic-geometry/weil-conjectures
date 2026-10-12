/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Flat.Basic
public import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Topology.SkyscraperComplex

/-!
# Stalks of flat sheaves of modules

Source: Stacks Project, Modules, Lemma 17.17.2 (Tag 05NE), flat sheaf implies flat stalks
(blueprint: lem-pc-flat-sheaf-stalk-flat).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.RingedSpace

set_option autoImplicit false

/-- Every stalk of a flat sheaf of modules on a ringed space is flat over the stalk ring.
Source: Stacks Project, Modules, Lemma 17.17.2 (Tag 05NE), implication from sheaf flatness
(blueprint: lem-pc-flat-sheaf-stalk-flat).

Proof:
1. Fix `x` and an exact three-term complex of modules over the stalk ring. Its termwise
   skyscraper complex is exact and has the original complex as its stalk at `x`, by
   `lem-pc-skyscraper-complex`.
2. Flatness of `F`, defined by `def-pc-flat-sheaf-modules`, says that tensoring this
   skyscraper complex on the right with `F` preserves exactness.
3. Stalk exactness (`lem-weil-pbc-module-stalk-exact`) and the natural stalk-tensor
   isomorphism (`lem-pc-ringed-space-module-stalk-tensor`) identify the resulting exact
   stalk complex with the original complex tensored with `F_x`. Thus right tensoring
   with `F_x` preserves exact sequences, which is `Module.Flat` over the stalk ring. -/
theorem flat_stalk_of_isFlat (X : RingedSpace.{u})
    (F : SheafOfModules.{u} (moduleRings X))
    (hF : SheafOfModules.IsFlat F) (x : X) :
    Module.Flat (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj F) := by
  sorry

end AlgebraicGeometry.RingedSpace
