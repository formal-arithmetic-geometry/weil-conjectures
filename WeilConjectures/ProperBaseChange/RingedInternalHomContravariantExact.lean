/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison

/-! # Contravariant exactness of derived internal Hom

Source: Stacks Project, Tag 08JC (lemma-RHom-triangulated).
(blueprint: lem-weil-pbc-ringed-internal-hom-contravariant-exact).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

attribute [local irreducible] CategoryTheory.homComplexFunctor CategoryTheory.homComplexπ
  CategoryTheory.derivedInternalHom

section
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{u})

private abbrev Modules := SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

attribute [local instance 10000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive

private instance : IsGrothendieckAbelian.{u} (Modules J R) :=
  SheafOfModules.isGrothendieckAbelian _

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

private instance : MonoidalPreadditive (Modules J R) := (SheafOfModules.tensorClosed R).1.some

attribute [local irreducible] SheafOfModules.homObj SheafOfModules.homObjMap
  MonoidalClosed.pre

-- A fixed name prevents repeated expansion of the closed structure in conversion goals.
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]

end

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.monoidalClosed

end CategoryTheory
