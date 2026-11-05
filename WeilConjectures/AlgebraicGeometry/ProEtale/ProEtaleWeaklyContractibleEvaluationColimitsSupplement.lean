/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationExact
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits

/-!
# Evaluation at affine weakly contractible pro-etale objects

Source: Stacks Project, Tags 0946 (1), 03DA and 0935 (2)
(blueprint: lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.Scheme.ProEt

end AlgebraicGeometry.Scheme.ProEt
