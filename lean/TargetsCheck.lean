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

/-!
# Library target statements

Imports the modules of the six target declarations of `Challenge` and nothing else; what this
file reaches is what the targets need. `tools/target_types.sh check` compares their elaborated
types with Challenge and prints their axioms. See `coord/target-migration.md`.
-/

@[expose] public section
