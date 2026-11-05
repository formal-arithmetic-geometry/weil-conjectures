/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Localized Hom boundaries and null-homotopies

Source: Stacks Project, Tag 0A8X, differential of the Hom complex,
and Equation 0A8Y, degree zero.
(blueprint: lem-pur-localized-hom-complex-boundaries)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite
namespace CategoryTheory

-- Package the definitional restriction comparison once; rechecking its maps is expensive.

end CategoryTheory
