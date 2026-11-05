/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.ProperBaseChange.BilinearHomComplexSupplement
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex

/-! # Coefficient Hom complexes over a ring-sheaf extension

Source: Stacks Project, Algebraization, Tag 099I
(blueprint: lem-weil-pbc-restricted-coefficient-hom-complex).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- Limit preservation gives a small proof of the required sheaf-composition instance.
attribute [local instance 0] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

end SheafOfModules
