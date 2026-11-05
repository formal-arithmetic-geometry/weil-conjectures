/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The Brown-hypotheses bundle

Source: blueprint latest, sec-six-functors-basics/sk-lem-brown-hypotheses/_section.md.
The definition and canonical instance abbreviations are shared by the unresolved
arbitrary-field assertion and the proved criteria. This module contains no compactness
assertion and imports no coefficient-specific compactness proof.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.all false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace CategoryTheory

attribute [local instance 30000] brownHypothesesCondensedMonoidal

attribute [local instance 30000] brownHypothesesCondensedBraided

attribute [local instance 30000] brownHypothesesSheafMonoidal

attribute [local instance 30000] brownHypothesesSheafBraided

attribute [local instance 30000] brownHypothesesCoefficientMonObj

attribute [local instance 30000] brownHypothesesModuleMonoidalClosed

-- Use the direct sheaf braiding when synthesizing the module-object tensor structure.
-- Reducing both the symmetric and braided localization constructions is expensive.
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar

end CategoryTheory
