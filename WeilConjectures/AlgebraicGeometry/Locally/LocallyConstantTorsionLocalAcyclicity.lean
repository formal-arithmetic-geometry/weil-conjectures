/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.GroupTheory.OrderOfElement
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalConstantComparison
import WeilConjectures.AlgebraicGeometry.Constant.ConstantTorsionAcyclicDevissage
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Local acyclicity for locally constant torsion coefficients

Source: Stacks Project, Tag 0GJR, lemma-locally-acyclic-locally-constant
(blueprint: lem-weil-pbc-locally-constant-torsion-local-acyclicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
