/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Exact Hom and K-flat dual computations for a strictly perfect local complex

Source: Stacks Project, Tag 08DQ, proof of lemma-dual-perfect-complex;
Tag 08DM, the bounded Hom calculation.
(blueprint: lem-pc-strictly-perfect-local-hom-computations).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

open scoped ZeroObject

namespace AlgebraicGeometry

end AlgebraicGeometry
