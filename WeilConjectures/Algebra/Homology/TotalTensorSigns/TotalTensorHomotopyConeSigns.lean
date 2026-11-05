/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated
import WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Signed tensor homotopies and mapping cones

Source: Stacks Project, Tags 06YM, 06YP, 0G6E, 0FNH and 0GWR;
derived.tex, definition-cone and definition-distinguished-triangle.
(blueprint: lem-weil-pbc-total-tensor-homotopy-cone-signs)
-/

@[expose] public noncomputable section

set_option autoImplicit false
attribute [local instance 10000] CategoryTheory.functorCategoryPreadditive
attribute [local instance 10000] SheafOfModules.instPreadditive
attribute [local instance 10000] HomologicalComplex.instPreadditive
attribute [local instance 10000] HomologicalComplex.instLinear
attribute [local instance 10000] CategoryTheory.Functor.preservesZeroMorphisms_of_additive
set_option synthInstance.maxSize 4096

universe u v r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open CochainComplex HomologicalComplex

attribute [local irreducible] SheafOfModules.monoidalCategory

namespace SheafOfModules.TotalTensorSigns

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

attribute [local instance 10000] coefficientCompose
  SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local instance 20000] modulesAbelian

namespace Generic

universe d e

variable (D : Type d) [Category.{e} D] [Abelian D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]
  [HasCoproducts.{0} D]

end Generic

attribute [local instance] Generic.genericTotalExists

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex

namespace Generic

universe d e

variable (D : Type d) [Category.{e} D] [Abelian D] [HasBinaryBiproducts D]
  [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D]

variable [HasCoproducts.{0} D]

end Generic

end SheafOfModules.TotalTensorSigns
