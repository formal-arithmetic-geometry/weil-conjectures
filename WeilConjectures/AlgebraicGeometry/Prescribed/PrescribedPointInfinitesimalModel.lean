/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Finite reduced points and their first infinitesimal neighbourhood

Source: blueprint, finite-cover-curve proof, paragraph 2; Stacks Project, Tag 01IN.
(blueprint: lem-zl-prescribed-point-infinitesimal-model).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ChangeOfRings TensorProduct

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local irreducible] tensorPullback Scheme.Modules.pullback
  tensorSectionsUnit prescribedPointJet

end

end AlgebraicGeometry
