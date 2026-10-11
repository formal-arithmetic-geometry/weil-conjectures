/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintainer L
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.FieldExtension
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk

/-!
# The target modules

Imports the modules of the targets and nothing else (`stages/2-statements.md` §4); what this
file reaches is what the targets need.

Decision of the human (2026-10-12 04:20 +08, `GOAL.md`): the targets are five declarations of
the source repository (branch `slopmaster2` at `7d675a263`):

- `AlgebraicGeometry.Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine`
  (`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`);
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper`
  (`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`);
- `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isAlgClosed` and
  `AlgebraicGeometry.IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed`
  (`WeilConjectures.AlgebraicGeometry.Curve.FieldExtension`);
- `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity`
  (`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty`; not locked until
  the upstream side answers).
-/

@[expose] public section

