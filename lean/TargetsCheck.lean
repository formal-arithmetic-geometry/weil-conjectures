/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintainer L
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk
public import WeilConjectures.AlgebraicGeometry.Curve.FieldExtension
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.Statement
public import Sheaf.Targets.EtaleSmooth
public import Sheaf.Targets.EtaleSmoothRing
public import WeilConjectures.PoincareDuality.Poincare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
public import WeilConjectures.SmoothPurity.Defs

/-!
# Library target statements

Imports the modules of the six target declarations of `Challenge` (batch 1), of the four
batch-2 targets, of smooth purity (batch 3), of Poincare duality (batch 4) and of the Weil
conjectures (batch 5, `WeilConjectures.Statement`). What this
file reaches is what the targets need. `tools/target_types.sh check` compares their elaborated
types with Challenge and prints their axioms. See `coord/target-migration.md`.
-/

@[expose] public section
