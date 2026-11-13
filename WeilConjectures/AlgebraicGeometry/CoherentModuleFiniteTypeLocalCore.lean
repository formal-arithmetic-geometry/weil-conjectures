/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict

import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalRestrict
import WeilConjectures.AlgebraicGeometry.CoherentModuleFiniteTypeLocalCover

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry
/-- The finite-type clauses of locality for coherent modules.
Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Lemma 01B6. -/
theorem coherent_module_finite_type_local_core
    (X : Scheme.{u}) (F : X.Modules) (I : Type u)
    (U : I → X.Opens) (hU : ⨆ i, U i = ⊤) :
    (RingedSpace.IsCoherent X.toRingedSpace F →
      ∀ (W : X.Opens),
        (Scheme.Modules.restrictFunctor W.ι).obj F |>.IsFiniteType) ∧
      ((∀ (i : I), RingedSpace.IsCoherent (U i).toScheme.toRingedSpace
          ((Scheme.Modules.restrictFunctor (U i).ι).obj F)) → F.IsFiniteType) := by
  constructor
  · intro hF W
    exact coherent_module_finite_type_local_restrict X F hF W
  · intro hF
    exact coherent_module_finite_type_local_cover X F I U hU hF
end AlgebraicGeometry
