/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge

/-! # Descent of a termwise coefficient map
Source: Stacks Project, Tags 06XN, 05SU and 06YY.
(blueprint: lem-sbc-derived-coefficient-map-descent)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

end CategoryTheory.Functor
