/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Sheaf.Topology.PresheafModuleStalkFunctor

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
  sorry

end AlgebraicGeometry.Scheme.Modules
