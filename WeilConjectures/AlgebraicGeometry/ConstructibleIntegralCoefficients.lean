/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift

import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsForward
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficientsBackward
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance

/-!
# Constructibility of torsion sheaves with integral coefficients

Source: Stacks Project, Tags 03RW and 095E; the comparison of (2) and (3)
for torsion sheaves and the canonical integral module structure.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
