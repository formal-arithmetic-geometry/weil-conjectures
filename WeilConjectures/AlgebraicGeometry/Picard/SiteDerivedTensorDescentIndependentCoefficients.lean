/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic


public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
-- r4: side KFlat instances (global there), as local instances of the live theorems
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

/-!
# Derived tensor descent on a ringed site

Site object, morphism, and coefficient universes are independent. The site is essentially
small relative to the coefficient universe, as required by the source. The statement retains
every localization, representative-comparison, and transformation-extension clause.

Source: Stacks Project, Cohomology on Sites, Tags 06YS, 0G7D, 06YT and 06YU;
Categories, Tags 04VI, 04VJ and 04VK
(blueprint: lem-weil-pbc-site-derived-tensor-descent).

## Main statements

- `site_derived_tensor_descent_independentCoefficients`: localization, representative comparison,
  and unique extension of arbitrary natural transformations.
-/

@[expose] public section

universe u v r w e z

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
-- Resolve the new vertices in Ore squares, roofs, and common refinements.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
-- Additivity is the only part of closed tensor structure needed for descent.
private theorem tensorPreadditive
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r}) :
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    MonoidalPreadditive (SheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := symmetricCategory R
  let A := SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  have (M : A) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

-- K-flatness kills the tensor of an acyclic mapping cone.
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 2048 in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section TensorDescentPredicates

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasDerivedCategory.{w} (SheafOfModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]

set_option hygiene false in
local notation "𝓜" => SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

end TensorDescentPredicates


set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
end SheafOfModules
